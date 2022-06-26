#!/usr/bin/env python3
# ----------------------------------
#
# Module kbo.py

"""
This is an implementation of the Knuth Bendix Ordering (KBO)
Based on following definition:

Let >F be a precedence on F, ϕ a weight function admissible
to >F, and s, t ∈ Term(F, V). Then s >kbo t if

    s ≡ f(s1,... , sn), t ≡ g(t1,... , tm), and
        (1) |s|_x ≥ |t|_x for all x ∈ V and
        (2a) ϕ(s) > ϕ(t) or
        (2b) ϕ(s) = ϕ(t), f >F g or
        (2c) ϕ(s) = ϕ(t), f = g, and there is some k with
             s1 ≡ t1,... , s_k−1 ≡ t_k−1, s_k >kbo t_k,
    or s ≡ f(s1,... , sn), t ≡ x ∈ V, and x ∈ Var(s).
"""
import unittest

from prover.clauses.literals import parseAtom
from prover.optimizations.kbo import *
from prover.optimizations.ocb import OCBCell


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
