#!/usr/bin/env python3
# ----------------------------------
#
# Module ocb.py

"""

"""
import unittest

from terms import string2Term


class OCBCell:
    def __init__(self, dataval=None, weights=None, var_weight=1):
        self.sig_size = dataval
        self.weights = weights
        self.var_weight = var_weight
        self.nextcell = None


class LinkedList:
    def __init__(self, initocbcell=None):
        self.initOCBCell = initocbcell


class TestOCB(unittest.TestCase):
    """
    Test basic ocb functions.
    """

    def testOCB(self):
        self.ocb1 = OCBCell(1, [1, 1], 1)
        self.ocb2 = OCBCell(2)
        self.ocb1.nextcell = self.ocb2
        self.list = LinkedList(self.ocb1)
        self.assertTrue(self.ocb1.weights == [1, 1])
        self.assertTrue(self.ocb1.nextcell.sig_size == 2)
        self.assertTrue(self.list.initOCBCell.nextcell.sig_size == 2)

if __name__ == '__main__':
    unittest.main()
