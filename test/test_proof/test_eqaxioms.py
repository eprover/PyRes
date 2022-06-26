#!/usr/bin/env python3
# ----------------------------------
#
# Module eqaxioms.py

"""
Copyright 2019 Stephan Schulz, schulz@eprover.org

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

from prover.proof.eqaxioms import *
from prover.clauses.terms import *


class TestEqAxioms(unittest.TestCase):
    """
    Test cases for equality axiom generation.
    """

    def setUp(self):
        """
        """
        print()

    def testEquivAxioms(self):
        """
        Test that the equivalence axioms are generated (or at least
        provide coverage ;-).
        """
        ax = generateEquivAxioms()
        print(ax)
        self.assertEqual(len(ax), 3)

    def testVarStuff(self):
        """
        Test variable and premise generation.
        """
        variables = generateVarList("X", 4)
        self.assertTrue("X1" in variables)
        self.assertTrue("X4" in variables)
        self.assertTrue("X5" not in variables)
        self.assertTrue("Y1" not in variables)
        self.assertEqual(len(variables), 4)
        print(variables)

        lits = generateEqPremise(3)
        self.assertEqual(len(lits), 3)
        print(lits)

    def testCompatibility(self):
        """
        Test that compatibility axioms are generated as expected.
        """
        ax = generateFunCompatAx("f", 3)
        self.assertEqual(len(ax), 4)
        print(ax)

        ax = generatePredCompatAx("p", 5)
        self.assertEqual(len(ax), 7)
        print(ax)

        sig = Signature()
        sig.addFun("f", 2)
        sig.addPred("p", 3)
        sig.addFun("a", 0)

        tmp = generateCompatAxioms(sig)
        # Note: No axiom for a
        self.assertEqual(len(tmp), 2)
