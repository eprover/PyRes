#!/usr/bin/env python2.7
# ----------------------------------
#
# Module clause.py

"""
A simple implementation of first-order clauses.

See literals.py for the definition of atoms and literals.

A logical clause in our sense is a multi-set of literals, implicitly
representing the universally quantified disjunction of these literals.


The set of all clauses for a given signature is denoted as
Clauses(P,F,V).

We represent a clause as a list of literals. The actual clause data
structure contains additional information that is useful, but not
strictly necessary from a clogic/alculus point of view.


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
from lexer import Token,Lexer
from resolution import resolution, factor
from clauses import parseClause
from clausesets import ClauseSet


def computeAllResolvents(clause, clauseset):
    """
    Compute all binary resolvents between a given clause and all
    clauses in clauseset.
    """
    res = []
    for lit in xrange(len(clause)):
        partners = \
                 clauseset.getResolutionLiterals(clause.getLiteral(lit))
        for (cl2, lit2) in partners:
            resolvent = resolution(clause, lit, cl2, lit2)
            if resolvent!=None:
                res.append(resolvent)
    return res


def computeAllFactors(clause):
    """
    Compute all (direkt) factors of clause.
    """
    res = []
    for i in xrange(len(clause)):
        for j in xrange(i+1, len(clause)):
            fact = factor(clause, i, j)
            if fact:
                res.append(fact)
    return res
    

class TestInferences(unittest.TestCase):
    """
    Unit test class for simple resolution inference control.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print
        spec = """
cnf(g1, negated_conjecture, ~c).
cnf(c1, axiom, a|b|c).
cnf(c2, axiom, b|c).
cnf(c3, axiom, c).
"""
        lex  = Lexer(spec)
        self.conj = parseClause(lex)
        self.cset = ClauseSet()
        self.cset.parse(lex)

        cstr = "cnf(ftest, axiom, p(X)|~q|p(a)|~q|p(Y))."
        lex = Lexer(cstr)
        self.fclause = parseClause(lex)
       
    def testSetResolution(self):
        """
        Test that forming resolvents between a clause and a clause set
        works. 
        """
        res = computeAllResolvents(self.conj, self.cset)
        print res

        
    def testFactoring(self):
        """
        Test full factoring of a clause.
        """
        res = computeAllFactors(self.fclause)
        print res


if __name__ == '__main__':
    unittest.main()
