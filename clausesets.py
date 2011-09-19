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
    A class representing a clause set (or, more precisely,
    a multi-set of clauses). 

    A clause optionally supports heuristic ordering of its clauses. If
    a list of heuristic functions is configured at creation time of
    the clause set, all clauses inserted into the set are evaluated
    according to all criteria. The clause set support extraction of
    the "best" clause according to any of the configured heuristics.
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

    def __len__(self):
        """
        Return number of clauses in set.
        """
        return len(self.clauses)

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
%------------------------------------------------------------------------------
% File     : PUZ001-1 : TPTP v4.1.0. Released v1.0.0.
% Domain   : Puzzles
% Problem  : Dreadbury Mansion
% Version  : Especial.
%            Theorem formulation : Made unsatisfiable.
% English  : Someone who lives in Dreadbury Mansion killed Aunt Agatha.
%            Agatha, the butler, and Charles live in Dreadbury Mansion,
%            and are the only people who live therein. A killer always
%            hates his victim, and is never richer than his victim.
%            Charles hates no one that Aunt Agatha hates. Agatha hates
%            everyone except the butler. The butler hates everyone not
%            richer than Aunt Agatha. The butler hates everyone Aunt
%            Agatha hates. No one hates everyone. Agatha is not the
%            butler. Therefore : Agatha killed herself.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [MB88]  Manthey & Bry (1988), SATCHMO: A Theorem Prover Implem
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :   12 (   2 non-Horn;   5 unit;  12 RR)
%            Number of atoms       :   21 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   3 constant; 0-0 arity)
%            Number of variables   :    8 (   0 singleton)
%            Maximal term depth    :    1 (   1 average)
% SPC      : CNF_UNS_EPR

% Comments : Modified from the [MB88] version to be unsatisfiable, by Geoff
%            Sutcliffe.
%          : Also known as "Who killed Aunt Agatha"
%------------------------------------------------------------------------------
cnf(agatha,hypothesis,
    ( lives(agatha) )).

cnf(butler,hypothesis,
    ( lives(butler) )).

cnf(charles,hypothesis,
    ( lives(charles) )).

cnf(poorer_killer,hypothesis,
    ( ~ killed(X,Y)
    | ~ richer(X,Y) )).

cnf(different_hates,hypothesis,
    ( ~ hates(agatha,X)
    | ~ hates(charles,X) )).

cnf(no_one_hates_everyone,hypothesis,
    ( ~ hates(X,agatha)
    | ~ hates(X,butler)
    | ~ hates(X,charles) )).

cnf(agatha_hates_agatha,hypothesis,
    ( hates(agatha,agatha) )).

cnf(agatha_hates_charles,hypothesis,
    ( hates(agatha,charles) )).

cnf(killer_hates_victim,hypothesis,
    ( ~ killed(X,Y)
    | hates(X,Y) )).

cnf(same_hates,hypothesis,
    ( ~ hates(agatha,X)
    | hates(butler,X) )).

cnf(butler_hates_poor,hypothesis,
    ( ~ lives(X)
    | richer(X,agatha)
    | hates(butler,X) )).

%----Literal dropped from here to make it unsatisfiable
cnf(prove_neither_charles_nor_butler_did_it,negated_conjecture,
    ( killed(butler,agatha)
    | killed(charles,agatha) )).

%------------------------------------------------------------------------------
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

        # Check if FIFO returns clauses in order.
        self.assertEqual(len(clauses), 12)
        c1 = clauses.extractBest(1)
        self.assertEqual(c1.name, "agatha")
        c2 = clauses.extractBest(1)
        self.assertEqual(c2.name, "butler")
        c3 = clauses.extractBest(1)
        self.assertEqual(c3.name, "charles")

        

if __name__ == '__main__':
    unittest.main()
