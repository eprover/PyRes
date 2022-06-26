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

from prover.optimizations.ocb import *
from test.convenience import string2Term


class TestOCB(unittest.TestCase):
    """
    Test basic ocb functions.
    """

    def setUp(self):
        self.example1 = "g(X, f(b))"
        self.t1 = string2Term(self.example1)
        self.example2 = "g(X, h(b))"
        self.t2 = string2Term(self.example2)
        self.ocb = OCBCell()
        self.ocb.insert2dic(self.t1)

    """
    Test basic ocb functions.
    """

    def testOCB(self):
        self.assertEqual(self.ocb.ocb_funs.keys(), {"b", "f", "g"})
        print(self.ocb.ocb_funs.values())
        print(self.ocb.ocb_funs)
        print(self.ocb.var_weight)
        self.ocb.insert2dic(self.t2)
        self.assertEqual(self.ocb.ocb_funs.keys(), {"b", "f", "g", "h"})
        print(self.ocb.ocb_funs)

        # self.ocb1 = OCBCell(1, [1, 1], 1)
        # self.ocb2 = OCBCell(2)
        # self.ocb1.nextcell = self.ocb2
        # self.list = LinkedList(self.ocb1)
        # self.assertTrue(self.ocb1.weights == [1, 1])
        # self.assertTrue(self.ocb1.nextcell.sig_size == 2)
        # self.assertTrue(self.list.initOCBCell.nextcell.sig_size == 2)

