#!/usr/bin/env python3
# ----------------------------------
#
# Module simplesat.py

"""
Minimalistic implementation of the given-clause algorithm for
saturation of clause sets under the rules of the resolution calculus.

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
from clausesets import ClauseSet, HeuristicClauseSet
import heuristics
from rescontrol import computeAllResolvents, computeAllFactors
from subsumption import forwardSubsumption, backwardSubsumption



class SimpleProofState(object):
    """
    Top-level data structure for the prover. The complete knowledge
    base is split into two sets, processed clauses and unprocessed
    clauses. These are represented here as individual clause sets. The
    main algorithm "processes" clauses and moves them from the
    unprocessed into the processed set. Processing typically generates
    several new clauses, which are direct consequences of the given
    clause and the processed claues. These new clauses are added to
    the set of unprocessed clauses.
    """
    def __init__(self, clauses):
        """
        Initialize the proof state with a set of clauses.
        """
        self.unprocessed = ClauseSet()                                    
        self.processed   = ClauseSet()
        for c in clauses.clauses:
            self.unprocessed.addClause(c)
        
    def processClause(self):
        """
        Pick a clause from unprocessed and process it. If the empty
        clause is found, return it. Otherwise return None.
        """
        given_clause = self.unprocessed.extractFirst()
        given_clause = given_clause.freshVarCopy()
        print("#", given_clause)
        if given_clause.isEmpty():
            # We have found an explicit contradiction
            return given_clause
        
        new = []
        factors    = computeAllFactors(given_clause)
        new.extend(factors)
        resolvents = computeAllResolvents(given_clause, self.processed)
        new.extend(resolvents)

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


class TestSimpleProver(unittest.TestCase):
    """
    Unit test class for simple resolution inference control.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.spec1 = """
 cnf(axiom, a_is_true, a).
 cnf(negated_conjecture, is_a_true, ~a)."""

        self.spec2 = """
        cnf(axiom, humans_are_mortal, mortal(X)|~human(X)).
        cnf(axiom, socrates_is_human, human(socrates)).
        cnf(negated_conjecture, is_socrates_mortal, ~mortal(socrates)).
"""

        self.spec3 = """
cnf(p_or_q, axiom, p(a)).
cnf(taut, axiom, q(a)).
cnf(not_p, axiom, p(b)).
"""

    def evalSatResult(self, spec, provable):
        """
        Evaluate the result of a saturation compared to the expected
        result.
        """

        lex = Lexer(spec)
        problem = ClauseSet()
        problem.parse(lex)

        prover = SimpleProofState(problem)
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
                
        
    def testSaturation(self):
        """
        Test that saturation works.
        """
        self.evalSatResult(self.spec1, True)
        self.evalSatResult(self.spec2, True)
        self.evalSatResult(self.spec3, False)

if __name__ == '__main__':
    unittest.main()
