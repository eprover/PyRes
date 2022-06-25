#!/usr/bin/env python3
# ----------------------------------
#
# Module ocb.py

"""
Implementation of the order control block (ocb)
OCB contains weights for funs (Dict) and weight of variables (unsigned int)
"""
import unittest

from prover.optimizations.ocb import *


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


if __name__ == '__main__':
    unittest.main()
