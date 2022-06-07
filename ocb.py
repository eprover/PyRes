#!/usr/bin/env python3
# ----------------------------------
#
# Module ocb.py

"""
Implementation of the order control block (ocb)
OCB contains weights for funs (Dict) precendece of funs(Dict) and weight of variables (unsigned int)

Copyright 2010-2021 Stephan Schulz, schulz@eprover.org

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

from terms import *


class OCBCell:

    def __init__(self, ocb_funs=None, var_weight=None, ocb_funs_prec=None, ocb_signature=None):
        if var_weight is None:
            var_weight = {}
        if ocb_funs is None:
            ocb_funs = {}
        if ocb_funs_prec is None:
            ocb_funs_prec = {}
        if ocb_signature is None:
            ocb_signature = Signature

        self.ocb_funs = ocb_funs
        self.var_weight = var_weight
        self.ocb_funs_prec = ocb_funs_prec
        self.ocb_signature = ocb_signature

    """
    For Tests only:
    """

    def insert2dic(self, term, weights=None, var_weight=1):
        if weights is None:
            weights = [1] * len(termCollectFuns(term))
        elif len(termCollectFuns(term)) - len(weights) != 0:
            print("weights and funs don't match")
            assert False
        for idx, fun in enumerate(termCollectFuns(term)):
            self.ocb_funs.update({fun: weights[idx]})
        self.var_weight = var_weight
        i = 0
        for fun in self.ocb_funs:
            self.ocb_funs_prec.update({fun: i})
            i = i + 1

    def insertsig2dic(self, signature):
        self.ocb_signature = signature


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


if __name__ == '__main__':
    unittest.main()
