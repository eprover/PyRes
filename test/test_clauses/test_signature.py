#!/usr/bin/env python3
# ----------------------------------
#
# Module signature.py

"""
Copyright 2012-2019 Stephan Schulz, schulz@eprover.org

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

from prover.clauses.signature import Signature


class TestSignature(unittest.TestCase):
    """
    Test basic functionality of the signature data type.
    """

    def testSig(self):
        """
        Test signature object.
        """
        sig = Signature()

        sig.addFun("mult", 2)
        sig.addFun("a", 0)
        sig.addPred("weird", 4)

        print(sig)
        self.assertTrue(sig.isPred("weird"))
        self.assertTrue(not sig.isPred("unknown"))
        self.assertTrue(not sig.isPred("a"))
        self.assertTrue(sig.isFun("a"))
        self.assertTrue(sig.isConstant("a"))
        self.assertTrue(not sig.isFun("unknown"))
        self.assertTrue(not sig.isFun("weird"))

        self.assertEqual(sig.getArity("a"), 0)
        self.assertEqual(sig.getArity("weird"), 4)

