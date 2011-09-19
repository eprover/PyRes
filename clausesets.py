#!/usr/bin/env python2.7
# ----------------------------------
#
# Module clausesets.py

"""
Clause sets for maintaining sets of clauses, possibly sorted by
heuristical evaluation.

Copyright 2010-2011 Stephan Schulz, schulz@eprover.org

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program ; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston,
MA  02111-1307 USA 

The original copyright holder can be contacted as

Stephan Schulz
Hirschstrasse 35
76133 Karlsruhe
Germany
Email: schulz@eprover.org
"""

import unittest
from lexer import Lexer
from clauses import Clause, parseClause
from heuristics import FIFOEvaluation, SymbolCountEvaluation

class ClauseSet(object):
    """
    A class representing a clause set. Clause sets really are lists of
    clauses. Clause sets support heuristic evaluation of
    clauses. Clauses are evaluated when inserting them, according to
    several criteria. The lightest clause (by any of the critera) can
    be extracted. Since inserting is a lot more frequent, we search
    the list when extracting. This can be made a lot more efficient
    with clever data structures (e.g. trees or heaps).
    """
    def __init__(self, eval_functions=None):
        """
        Initialize the clause.
        """
        self.clauses  = []
        self.eval_functions = eval_functions
        
        
    def __repr__(self):
        """
        Return a string representation of the clause set.
        """
        return "\n".join([repr(clause) for clause in self.clauses])

    def addClause(self, clause):
        """
        Add a clause to the clause set. If the clause set supports
        heuristic evaluations, add the relevant evaluations to the
        clause. 
        """
        self.clauses.append(clause)
        if self.eval_functions:
            evals = [f(clause) for f in self.eval_functions]
            clause.addEval(evals)

    def __len__(self):
        """
        Return number of clauses in set.
        """
        return len(self.clauses)

    def extractBest(self, heuristic_index):
        """
        Extract and return the clause with the lowest weight according
        to the selected heuristic. If the set is empty, return None.
        """
        if self.clauses:
            best = 0
            besteval = self.clauses[0].evaluation[heuristic_index]
            for i in xrange(1, len(self.clauses)):
                if self.clauses[i].evaluation[heuristic_index] < besteval:
                    besteval = clauses[i].evaluation[heuristic_index]
                    best     = i
            return self.clauses.pop(best)
        else:
            return None
                    
    def parse(self, lexer):
        """
        Parse a sequence of clauses from lex and add them to the set.
        """
        while lexer.LookLit() == "cnf":
            clause = parseClause(lexer)
            self.addClause(clause)
    

class TestClauseSets(unittest.TestCase):
    """
    Unit test class for clause sets.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print
        self.spec ="""
cnf(c1,axiom,(f(X1,X2)=f(X2,X1))).
cnf(c2,axiom,(f(X1,f(X2,X3))=f(f(X1,X2),X3))).
cnf(c3,axiom,(g(X1,X2)=g(X2,X1))).
cnf(c4,axiom,(f(f(X1,X2),f(X3,g(X4,X5)))!=f(f(g(X4,X5),X3),f(X2,X1))|k(X1,X1)!=k(a,b))).
cnf(c5,axiom,(b=c|X1!=X2|X3!=X4|c!=d)).
cnf(c6,axiom,(a=b|a=c)).
cnf(c7,axiom,(i(X1)=i(X2))).
cnf(c8,axiom,(c=d|h(i(a))!=h(i(e)))).
"""
       
    def testClauseSetInit(self):
        """
        Test that clause set initialization and parsing work.
        """
        lexer = Lexer(self.spec)
        clauses = ClauseSet()
        clauses.parse(lexer)
        print clauses

        print "=========================================="

        clauses = ClauseSet([SymbolCountEvaluation(2,1), FIFOEvaluation()])
        lexer = Lexer(self.spec)
        clauses.parse(lexer)
        print clauses

        self.assertEqual(len(clauses), 8)
        c1 = clauses.extractBest(1)
        self.assertEqual(c1.name, "c1")
        c2 = clauses.extractBest(1)
        self.assertEqual(c2.name, "c2")

if __name__ == '__main__':
    unittest.main()
