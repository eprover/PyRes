"""
Copyright 2010-2019 Stephan Schulz, schulz@eprover.org

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
Auf der Altenburg 7
70376 Stuttgart
Germany
Email: schulz@eprover.org
"""

import unittest

from prover.clauses.literals import parseLiteral
from prover.clauses.clausesets import ClauseSet, HeuristicClauseSet, IndexedClauseSet
from prover.clauses.signature import Signature
from prover.optimizations.heuristics import PickGiven2
from prover.parser.lexer import Lexer


class TestClauseSets(unittest.TestCase):
    """
    Unit test class for clause sets.
    """

    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.spec = """
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

cnf(killer_hates_victim,hypothesis,
    ( ~ killed(X,Y)
    | hates(X,Y) )).

cnf(same_hates,hypothesis,
    ( ~ hates(agatha,X)
    | hates(butler,X) )).

cnf(agatha_hates_charles,hypothesis,
    ( hates(agatha,charles) )).

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

    def testClauseSetChanges(self):
        """
        Test that clause set initialization and parsing work.
        """
        lexer = Lexer(self.spec)
        clauses = ClauseSet()
        clauses.parse(lexer)
        print(clauses)
        oldlen = len(clauses)
        c = clauses.clauses[0]
        clauses.extractClause(c)
        self.assertEqual(len(clauses), oldlen - 1)

        sig = Signature()
        clauses.collectSig(sig)
        print(sig)

    def testClauseSetHeuristics(self):
        """
        Test the evaluation and heuristic methods.
        """
        print("==========================================")
        clauses = HeuristicClauseSet(PickGiven2)
        lexer = Lexer(self.spec)
        parsed = clauses.parse(lexer)
        self.assertEqual(parsed, 12)
        print(clauses)

        # Check if FIFO returns clauses in order.
        self.assertEqual(len(clauses), 12)
        c1 = clauses.extractBestByEval(1)
        self.assertEqual(c1.name, "agatha")
        c2 = clauses.extractBestByEval(1)
        self.assertEqual(c2.name, "butler")
        c3 = clauses.extractFirst()
        self.assertEqual(c3.name, "charles")
        c = clauses.extractBestByEval(0)
        while c is not None:
            c = clauses.extractBestByEval(0)

        print("==========================================")
        clauses = HeuristicClauseSet(PickGiven2)
        lexer = Lexer(self.spec)
        clauses.parse(lexer)
        c = clauses.extractBest()
        while c is not None:
            print(c)
            c = clauses.extractBest()
        c = clauses.extractFirst()
        self.assertEqual(c, None)

    def testIndexedClauseSetChanges(self):
        """
        Test that clause set initialization and parsing work.
        """
        lexer = Lexer(self.spec)
        clauses = IndexedClauseSet()
        clauses.parse(lexer)
        print(clauses)
        oldlen = len(clauses)
        c = clauses.clauses[0]
        clauses.extractClause(c)
        self.assertEqual(len(clauses), oldlen - 1)

        sig = clauses.collectSig()
        print(sig)

    def testResPositions(self):
        """
        Test the the function returning all possible literal positions
        of possible resolution partner works. The default version
        should return the clause/position pairs of all literals in the
        clause set.
        """
        lexer = Lexer(self.spec)
        clauses = ClauseSet()
        clauses.parse(lexer)

        lexer = Lexer("hates(X,agatha)")
        lit = parseLiteral(lexer)
        pos = clauses.getResolutionLiterals(lit)
        self.assertTrue(len(pos), 21)
        print(pos)

    def testResIndexedPositions(self):
        """
        Test the the function returning all possible literal positions
        of possible resolution partner vie indexing works. The indexed
        version should return the clause/position pairs of all
        literals with opposite polarity and the same top symbol as the
        query literal.
        """
        lexer = Lexer(self.spec)
        clauses = IndexedClauseSet()
        clauses.parse(lexer)

        lexer = Lexer("hates(X,agatha)")
        lit = parseLiteral(lexer)
        pos = clauses.getResolutionLiterals(lit)
        self.assertTrue(len(pos), 6)
        print(pos)
