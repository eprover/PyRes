#!/usr/bin/env python3
# ----------------------------------
#
# Module clausesets.py

"""
Clause sets for maintaining sets of clauses, possibly sorted by
heuristical evaluation.

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
from lexer import Lexer
from signature import Signature
from literals import parseLiteral
from clauses import Clause, parseClause
from heuristics import PickGiven2
from indexing import ResolutionIndex, SubsumptionIndex

class ClauseSet(object):
    """
    A class representing a clause set (or, more precisely,
    a multi-set of clauses).
    """
    def __init__(self, clauses = []):
        """
        Initialize the clause.
        """
        self.clauses = list(clauses)

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
        Add a clause to the clause set.
        """
        self.clauses.append(clause)

    def extractClause(self, clause):
        """
        Remove a clause to the clause set and return it.
        """
        self.clauses.remove(clause)
        return clause

    def collectSig(self, sig=None):
        """
        Collect function- and predicate symbols into the signature. If
        none exists, create it. Return the signature
        """
        if not sig:
            sig = Signature()

        for i in self.clauses:
            i.collectSig(sig)
        return sig

    def extractFirst(self):
        """
        Extract and return the first clause.
        """
        if self.clauses:
            clause = self.clauses.pop(0)
            return clause
        else:
            return None

    def getResolutionLiterals(self, lit):
        """
        Return a list of tuples (clause, literal-index) such that the
        set includes at least all literals that can potentially be
        resolved against lit. In the naive and obviously correct first
        implementation, this simply returns a list of all
        literal-indices for all clauses.
        """
        res = [(c, i) for c in self.clauses for i in range(len(c)) if
               c.getLiteral(i).isInferenceLit()]
        return res

    def getSubsumingCandidates(self, queryclause):
        """
        Return a subset (as a list) of the set containing at least all
        clauses potentially subsuming queryclause. For a plain
        ClauseSet, we just return all clauses in the set. 
        """
        return self.clauses

    def getSubsumedCandidates(self, queryclause):
        """
        Return a subset (as a list) of the set containing at least the
        clauses  potentially subsumed by queryclause). For a plain
        ClauseSet, we just return all clauses in the set.
        """
        return self.clauses
        

    def parse(self, lexer):
        """
        Parse a sequence of clauses from lex and add them to the
        set. Return number of clauses parsed.
        """
        count = 0
        while lexer.LookLit() == "cnf":
            clause = parseClause(lexer)
            self.addClause(clause)
            count = count+1
        return count


class HeuristicClauseSet(ClauseSet):
    """
    A class representing a clause set (or, more precisely, a multi-set
    of clauses) with heuristic evaluations.

    All clauses inserted into the set are evaluated
    according to all criteria. The clause set support extraction of
    the "best" clause according to any of the configured heuristics.
    """
    def __init__(self, eval_functions):
        """
        Initialize the clause.
        """
        self.clauses  = []
        self.eval_functions = eval_functions


    def addClause(self, clause):
        """
        Add a clause to the clause set. If the clause set supports
        heuristic evaluations, add the relevant evaluations to the
        clause.
        """
        evals = self.eval_functions.evaluate(clause)
        clause.addEval(evals)
        ClauseSet.addClause(self, clause)

    def extractBestByEval(self, heuristic_index):
        """
        Extract and return the clause with the lowest weight according
        to the selected heuristic. If the set is empty, return None.
        """
        if self.clauses:
            best = 0
            besteval = self.clauses[0].evaluation[heuristic_index]
            for i in range(1, len(self.clauses)):
                if self.clauses[i].evaluation[heuristic_index] < besteval:
                    besteval = self.clauses[i].evaluation[heuristic_index]
                    best     = i
            return self.clauses.pop(best)
        else:
            return None

    def extractBest(self):
        """
        Extract and return the next "best" clause according to the
        evaluation scheme.
        """
        return self.extractBestByEval(self.eval_functions.nextEval())



class IndexedClauseSet(ClauseSet):
    """
    This is a normal clause set, augmented by indices that speeds up
    the finding of resolution and subsumption partners.
    """
    def __init__(self, clauses = []):
        """
        Create the two indices and call the superclass initializer. 
        """
        self.res_index = ResolutionIndex()
        self.sub_index = SubsumptionIndex()
        ClauseSet.__init__(self, clauses)

    def addClause(self, clause):
        """
        Add the clause to the indices, then use the  superclass
        function to add it to the actual set.
        """
        self.res_index.insertClause(clause)
        self.sub_index.insertClause(clause)
        ClauseSet.addClause(self, clause)

    def extractClause(self, clause):
        """
        Remove the clause from the indices, then use the  superclass
        function to remove it to the actual set.
        """
        self.res_index.removeClause(clause)
        self.sub_index.removeClause(clause)
        return ClauseSet.extractClause(self, clause)

    def getResolutionLiterals(self, lit):
        """
        Overwrite the original function with one based on indexing. 
        """
        return self.res_index.getResolutionLiterals(lit)

    def getSubsumingCandidates(self, queryclause):
        """
        Overwrite the original function with one based on indexing. 
        """
        return self.sub_index.getSubsumingCandidates(queryclause)

    def getSubsumedCandidates(self, queryclause):
        """
        Overwrite the original function with one based on indexing. 
        """
        return self.sub_index.getSubsumedCandidates(queryclause)


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
        self.assertEqual(len(clauses), oldlen-1)

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
        while c != None:
            c = clauses.extractBestByEval(0)

        print("==========================================")
        clauses = HeuristicClauseSet(PickGiven2)
        lexer = Lexer(self.spec)
        parsed = clauses.parse(lexer)
        c = clauses.extractBest()
        while c != None:
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
        self.assertEqual(len(clauses), oldlen-1)

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




if __name__ == '__main__':
    unittest.main()
