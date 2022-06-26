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

from prover.optimizations.kbo import *
from prover.optimizations.ocb import OCBCell
from prover.parser.lexer import Lexer
from prover.parser.parser import parseAtom
from test.convenience import string2Term


class TestKBO(unittest.TestCase):
    """
    Test basic kbo functions.
    """

    def setUp(self):
        self.example1 = "X"
        self.example2 = "Y"
        self.example3 = "g(X, f(b))"
        self.example4 = "$True"
        self.example5 = "g(X, h(a, b))"
        self.example6 = "g(X, h(X, a))"
        self.example7 = "g(Y, h(Y, Y))"
        self.example8 = "g(X, h(a))"
        self.example9 = "g(X, h(b))"

        self.t1 = string2Term(self.example1)
        self.t2 = string2Term(self.example2)
        self.t3 = string2Term(self.example3)
        self.t4 = string2Term(self.example4)
        self.t5 = string2Term(self.example5)
        self.t6 = string2Term(self.example6)
        self.t7 = string2Term(self.example7)
        self.t8 = string2Term(self.example8)
        self.t9 = string2Term(self.example9)

        self.input1 = "p(X)  q(f(X,a), b)  a!=b"
        lexer = Lexer(self.input1)
        self.a1 = parseAtom(lexer)
        self.a2 = parseAtom(lexer)
        self.a3 = parseAtom(lexer)

    def testkbocomparevars(self):
        """
        Test if the kbocomparevars() function work as expected.
        """
        self.assertTrue(kbocomparevars(self.t1, self.t1) == CompareResult.to_equal)
        self.assertTrue(kbocomparevars(self.t1, self.t3) == CompareResult.to_lesser)
        self.assertTrue(kbocomparevars(self.t3, self.t1) == CompareResult.to_greater)
        self.assertTrue(kbocomparevars(self.t1, self.t2) == CompareResult.to_uncomparable)
        self.assertTrue(kbocomparevars(self.t2, self.t3) == CompareResult.to_uncomparable)

    def testkbocompare(self):
        """
        Test if the kbocompare() function work as expected.
        """
        ocb = OCBCell()
        ocb.insert2dic(self.t4)
        ocb.insert2dic(self.t3)
        ocb.insert2dic(self.t8)
        ocb.insert2dic(self.t2)
        print("Ordering:")
        print(ocb.ocb_funs.keys())
        self.assertTrue(kbocompare(ocb, self.t1, self.t1) == CompareResult.to_equal)
        self.assertTrue(kbocompare(ocb, self.t1, self.t3) == CompareResult.to_lesser)
        self.assertTrue(kbocompare(ocb, self.t3, self.t1) == CompareResult.to_greater)
        self.assertTrue(kbocompare(ocb, self.t1, self.t2) == CompareResult.to_uncomparable)
        self.assertTrue(kbocompare(ocb, self.t2, self.t3) == CompareResult.to_uncomparable)
        self.assertTrue(kbocompare(ocb, self.t6, self.t3) == CompareResult.to_greater)
        self.assertTrue(kbocompare(ocb, self.t3, self.t6) == CompareResult.to_lesser)
        self.assertTrue(kbocompare(ocb, self.t5, self.t3) == CompareResult.to_greater)

        self.assertTrue(kbocompare(ocb, self.t7, self.t3) == CompareResult.to_uncomparable)
        self.assertTrue(kbocompare(ocb, self.t4, self.t3) == CompareResult.to_lesser)
        self.assertTrue(kbocompare(ocb, self.t3, self.t4) == CompareResult.to_greater)

        self.assertTrue(kbocompare(ocb, self.t3, self.t8) == CompareResult.to_lesser)
        self.assertTrue(kbocompare(ocb, self.t8, self.t3) == CompareResult.to_greater)

        self.assertTrue(kbocompare(ocb, self.t3, self.t3) == CompareResult.to_equal)
        self.assertTrue(kbocompare(ocb, self.t8, self.t9) == CompareResult.to_greater)
        self.assertTrue(kbocompare(ocb, self.t9, self.t8) == CompareResult.to_lesser)

        """
        Test with literals
        """
        ocb_lit = OCBCell()
        ocb_lit.insert2dic(self.a3)
        ocb_lit.insert2dic(self.a1)
        ocb_lit.insert2dic(self.a2)
        print(ocb_lit.ocb_funs.keys())
        self.assertTrue(kbocompare(ocb_lit, self.a1, self.a1) == CompareResult.to_equal)
        self.assertTrue(kbocompare(ocb_lit, self.a2, self.a2) == CompareResult.to_equal)
        self.assertTrue(kbocompare(ocb_lit, self.a3, self.a3) == CompareResult.to_equal)
        self.assertTrue(kbocompare(ocb_lit, self.a1, self.a2) == CompareResult.to_lesser)
        self.assertTrue(kbocompare(ocb_lit, self.a2, self.a3) == CompareResult.to_greater)
        self.assertTrue(kbocompare(ocb_lit, self.a1, self.a3) == CompareResult.to_uncomparable)
