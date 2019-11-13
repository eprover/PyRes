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
from idents import Ident
from lexer import Token,Lexer
from clausesets import ClauseSet, HeuristicClauseSet, IndexedClauseSet
import heuristics
from rescontrol import computeAllResolvents, computeAllFactors
from subsumption import forwardSubsumption, backwardSubsumption


class SearchParams(object):
    """
    A simple container for different parameter settings for the proof
    search.
    """
    def __init__(self,
                 heuristics = heuristics.PickGiven5,
                 delete_tautologies   = False,
                 forward_subsumption  = False,
                 backward_subsumption = False,
                 literal_selection    = None):
        """
        Initialize heuristic parameters.
        """
        self.heuristics           = heuristics
        """
        This defines the clause selection heuristic, i.e. the order in
        which uprocessed clauses are selected for processing.
        """
        self.delete_tautologies   = delete_tautologies
        """
        This determines if tautologies will be deleted. Tautologies in
        plain first-order logic (without equality) are clauses which
        contain two literals with the same atom, but opposite signs.
        """
        self.forward_subsumption  = forward_subsumption
        """
        Forward-subsumption checks the given clause against already
        processed clauses, and discards it if it is subsumed.
        """
        self.backward_subsumption = backward_subsumption
        """
        Backwars subsumption checks the processed clauses against the
        given clause, and discards all processed clauses that are
        subsumed.
        """
        self.literal_selection = literal_selection
        """
        Either None, or a function that selects a subset of negative
        literals from a set of negative literals (both represented as
        lists, not Python sets) as the inference literal.
        """



class ProofState(object):
    """
    Top-level data structure for the prover. The complete knowledge
    base is split into two sets, processed clauses and unprocessed
    clauses. These are represented here as individual clause sets. The
    main algorithm "processes" clauses and moves them from the
    unprocessed into the processed set. Processing typically generates
    several new clauses, which are direct consequences of the given
    clause and the processed claues. These new clauses are added to
    the set of unprocessed clauses.

    In addition to the clause sets, this data structure also maintains
    a number of counters for statistics on the proof search.
    """
    def __init__(self, params, clauses, silent=False, indexed=False):
        """
        Initialize the proof state with a set of clauses.
        """
        self.params = params
        self.unprocessed = HeuristicClauseSet(params.heuristics)

        if indexed:
            self.processed   = IndexedClauseSet()
        else:
            self.processed   = ClauseSet()
        for c in clauses.clauses:
            self.unprocessed.addClause(c)
        self.initial_clause_count = len(self.unprocessed)
        self.proc_clause_count    = 0
        self.factor_count         = 0
        self.resolvent_count      = 0
        self.tautologies_deleted  = 0
        self.forward_subsumed     = 0
        self.backward_subsumed    = 0
        self.silent               = silent

    def processClause(self):
        """
        Pick a clause from unprocessed and process it. If the empty
        clause is found, return it. Otherwise return None.
        """
        given_clause = self.unprocessed.extractBest()
        given_clause = given_clause.freshVarCopy()
        if not self.silent:
            print("#")
        if given_clause.isEmpty():
            # We have found an explicit contradiction
            return given_clause
        if self.params.delete_tautologies and \
           given_clause.isTautology():
            self.tautologies_deleted += 1
            return None
        if self.params.forward_subsumption and \
           forwardSubsumption(self.processed, given_clause):
            # If the given clause is subsumed by an already processed
            # clause, all releveant inferences will already have been
            # done with that more general clause. So we can discard
            # the given clause. We do keep count of how many clauses
            # we have dropped this way.
            self.forward_subsumed += 1
            return None

        if self.params.backward_subsumption:
            # If the given clause subsumes any of the already
            # processed clauses, it will "cover" for these less
            # general clauses in the future, so we can remove them
            # from the proof state. Again, we keep count of the number
            # of clauses dropped. This typically happens less often
            # than forward subsumption, because most heuristics prefer
            # smaller clauses, which tend to be more general (thus the
            # processed clauses are typically if not universally more
            # general than the new given clause).
            tmp = backwardSubsumption(given_clause, self.processed)
            self.backward_subsumed = self.backward_subsumed+tmp

        if(self.params.literal_selection):
            given_clause.selectInferenceLits(self.params.literal_selection)
        if not self.silent:
            print("#", given_clause)
        new = []
        factors    = computeAllFactors(given_clause)
        new.extend(factors)
        resolvents = computeAllResolvents(given_clause, self.processed)
        new.extend(resolvents)
        self.proc_clause_count = self.proc_clause_count+1
        self.factor_count = self.factor_count+len(factors)
        self.resolvent_count = self.resolvent_count+len(resolvents)

        self.processed.addClause(given_clause)

        for c in new:
            self.unprocessed.addClause(c)
        return None

    def saturate(self):
        """
        Main proof procedure. If the clause set is found
        unsatisfiable, return the empty clause as a witness. Otherwise
        return None.
        """
        while self.unprocessed:
            res = self.processClause()
            if res != None:
                return res
        else:
            return None

    def statisticsStr(self):
        """
        Return the proof state statistics in string form ready for
        output.
        """
        return """
# Initial clauses    : %d
# Processed clauses  : %d
# Factors computed   : %d
# Resolvents computed: %d
# Tautologies deleted: %d
# Forward subsumed   : %d
# Backward subsumed  : %d""" \
    %(self.initial_clause_count,
      self.proc_clause_count,
      self.factor_count,
      self.resolvent_count,
      self.tautologies_deleted,
      self.forward_subsumed,
      self.backward_subsumed)


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
            if res == None: # pragma: nocover
                print("# Bug: Should have found a proof!")
            else:
                print("# Proof found")
        else:
            self.assertEqual(res, None)
            if res != None: # pragma: nocover
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
        self.assertEqual(pm.delete_tautologies,   False)
        self.assertEqual(pm.forward_subsumption,  False)
        self.assertEqual(pm.backward_subsumption, False)

if __name__ == '__main__':
    unittest.main()
