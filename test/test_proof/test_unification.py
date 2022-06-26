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

from prover.proof.unification import *


class TestUnification(unittest.TestCase):
    """
    Test basic substitution functions.
    """

    def setUp(self):
        self.s1 = terms.string2Term("X")
        self.t1 = terms.string2Term("a")

        self.s2 = terms.string2Term("X")
        self.t2 = terms.string2Term("f(X)")

        self.s3 = terms.string2Term("X")
        self.t3 = terms.string2Term("f(Y)")

        self.s4 = terms.string2Term("f(X, a)")
        self.t4 = terms.string2Term("f(b, Y)")

        self.s5 = terms.string2Term("f(X, g(a))")
        self.t5 = terms.string2Term("f(X, Y))")

        self.s6 = terms.string2Term("f(X, g(a))")
        self.t6 = terms.string2Term("f(X, X))")

        self.s7 = terms.string2Term("g(X)")
        self.t7 = terms.string2Term("g(f(g(X),b))")

        self.s8 = terms.string2Term("p(X,X,X)")
        self.t8 = terms.string2Term("p(Y,Y,e)")

        self.s9 = terms.string2Term("f(f(g(X),a),X)")
        self.t9 = terms.string2Term("f(Y,g(Y))")

        self.s10 = terms.string2Term("f(f(g(X),a),g(X))")
        self.t10 = terms.string2Term("f(Y,g(Z))")

        self.s11 = terms.string2Term("p(X,g(a), f(a, f(a)))")
        self.t11 = terms.string2Term("p(f(a), g(Y), f(Y, Z))")

    def unif_test(self, s, t, success_expected):
        """
       Test if s and t can be unified. If yes, report the
       result. Compare to the expected result.
       """
        print("Trying to unify", term2String(s), "and", term2String(t))
        sigma = mgu(s, t)
        if success_expected:
            self.assertTrue(sigma)
            self.assertTrue(termEqual(sigma(s), sigma(t)))
            print(term2String(sigma(s)), term2String(sigma(t)), sigma)
        else:
            print("Failure")
            self.assertTrue(not sigma)
        print()

    def testMGU(self):
        """
        Test basic stuff.
        """
        print()
        self.unif_test(self.s1, self.t1, True)
        self.unif_test(self.s2, self.t2, False)
        self.unif_test(self.s3, self.t3, True)
        self.unif_test(self.s4, self.t4, True)
        self.unif_test(self.s5, self.t5, True)
        self.unif_test(self.s6, self.t6, True)
        self.unif_test(self.s7, self.t7, False)
        self.unif_test(self.s8, self.t8, True)

        self.unif_test(self.s9, self.t9, False)
        self.unif_test(self.s10, self.t10, True)
        self.unif_test(self.s11, self.t11, True)

        # Unification should be symmetrical
        # self.unif_test(self.t1, self.s1, True)
        # self.unif_test(self.t2, self.s2, False)
        # self.unif_test(self.t3, self.s3, True)
        # self.unif_test(self.t4, self.s4, True)
        # self.unif_test(self.t5, self.s5, True)
        # self.unif_test(self.t6, self.s6, True)
        # self.unif_test(self.t7, self.s7, False)
        # self.unif_test(self.t8, self.s8, True)
