#!/usr/bin/env python3
# ----------------------------------
#
# Module derivations.py

"""
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

from prover.clauses.derivations import *


class TestDerivations(unittest.TestCase):
    """
    """

    def setUp(self):
        print()

    def testDerivable(self):
        """
        Test basic properties of derivations.
        """
        o1 = Derivable()
        o2 = Derivable()
        o3 = Derivable()
        o3.setDerivation(flatDerivation("resolution", [o1, o2]))
        self.assertEqual(o1.getParents(), [])
        self.assertEqual(o2.getParents(), [])
        self.assertEqual(len(o3.getParents()), 2)
        print(o3)
        print(o3.derivation)
        o3.setDerivation(flatDerivation("factor", [o1]))
        print(o3.derivation)
        self.assertEqual(len(o3.getParents()), 1)

    def testProofExtraction(self):
        """
        Test basic proof extraction.
        """
        o1 = Derivable()
        o2 = Derivable()
        o3 = Derivable()
        o4 = Derivable()
        o5 = Derivable()
        o6 = Derivable()
        o7 = Derivable()
        o1.setDerivation(Derivation("eq_axiom"))
        print(repr(o1.derivation))
        o2.setDerivation(Derivation("input"))
        o3.setDerivation(flatDerivation("factor", [o1]))
        o4.setDerivation(flatDerivation("factor", [o3]))
        o5.setDerivation(flatDerivation("resolution", [o1, o2]))
        o6.setDerivation(Derivation("reference", [o5]))
        o7.setDerivation(flatDerivation("resolution", [o5, o1]))
        proof = o7.orderedDerivation()
        print(proof)
        self.assertEqual(len(proof), 4)
        self.assertTrue(o1 in proof)
        self.assertTrue(o2 in proof)
        self.assertTrue(o5 in proof)
        self.assertTrue(o7 in proof)

    def testOutput(self):
        """
        Test derivation output functions.
        """
        o1 = Derivable()
        o2 = Derivable()
        o3 = Derivable()
        o4 = Derivable()
        o1.setDerivation(Derivation("eq_axiom"))
        o2.setDerivation(Derivation("input"))
        o3.setDerivation(flatDerivation("resolution", [o1, o2]))
        enableDerivationOutput()
        self.assertTrue(o2.strDerivation() != "")
        self.assertTrue(o3.strDerivation() != "")
        self.assertTrue(o4.strDerivation() == "")
        disableDerivationOutput()
        self.assertTrue(o3.strDerivation() == "")
        self.assertTrue(o4.strDerivation() == "")
        toggleDerivationOutput()
        self.assertTrue(o3.strDerivation() != "")
        self.assertTrue(o4.strDerivation() == "")
