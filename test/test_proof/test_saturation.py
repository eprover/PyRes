#!/usr/bin/env python3
# ----------------------------------
#
# Module saturation.py

"""
Implementation of the given-clause algorithm for saturation of clause
sets under the rules of the resolution calculus. This improves on the
very basic implementation in simplesat in several ways.

- It supports heuristic clause selection, not just first-in first-out
- It supports tautology deletion
- It supports forward and backwards subsumption
- It keeps some statistics to enable the user to understand the
  practical impact of different steps of the algorithm better.

Most of these changes can be found in the function processClause() of
the ProofState class.

Copyright 2011-2019 Stephan Schulz, schulz@eprover.org

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

from prover.parser.lexer import Lexer
from prover.proof.saturation import *


class TestProver(unittest.TestCase):
    """
    Unit test class for simple resolution inference control.
    """

    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.params = SearchParams()
        self.params.delete_tautologies = True
        self.spec1 = """
 cnf(axiom, a_is_true, a).
 cnf(negated_conjecture, is_a_true, ~a)."""

        self.spec2 = """
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

        self.spec3 = """
cnf(p_or_q, axiom, p(X)|q(a)).
cnf(taut, axiom, p(X)|~p(X)).
cnf(not_p, axiom, ~p(a)).
"""

    def evalSatResult(self, spec, provable):
        """
        Evaluate the result of a saturation compared to the expected
        result.
        """

        lex = Lexer(spec)
        problem = ClauseSet()
        problem.parse(lex)

        prover = ProofState(self.params, problem)
        res = prover.saturate()

        if provable:
            self.assertNotEqual(res, None)
            if res is None:  # pragma: nocover
                print("# Bug: Should have found a proof!")
            else:
                print("# Proof found")
        else:
            self.assertEqual(res, None)
            if res is not None:  # pragma: nocover
                print("# Bug: Should not have  found a proof!")
            else:
                print("# No proof found")

        print(prover.statisticsStr())

    def testSaturation(self):
        """
        Test that saturation works.
        """
        self.evalSatResult(self.spec1, True)
        self.evalSatResult(self.spec2, True)
        self.evalSatResult(self.spec3, False)

    def testParamSet(self):
        """
        Test that parameter setting code works.
        """
        pm = SearchParams()
        self.assertEqual(pm.heuristics, heuristics.PickGiven5)
        self.assertEqual(pm.delete_tautologies, False)
        self.assertEqual(pm.forward_subsumption, False)
        self.assertEqual(pm.backward_subsumption, False)


if __name__ == '__main__':
    unittest.main()
