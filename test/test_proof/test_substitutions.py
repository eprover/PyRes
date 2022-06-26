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

import prover.clauses.conversion
from test.convenience import string2Term
from prover.proof.substitutions import *


class TestSubst(unittest.TestCase):
    """
    Test basic substitution functions.
    """
    def setUp(self):
        self.t1 = string2Term("f(X, g(Y))")
        self.t2 = string2Term("a")
        self.t3 = string2Term("b")
        self.t4 = string2Term("f(a, g(a))")
        self.t5 = string2Term("f(a, g(b))")

        self.sigma1 = Substitution([("X", self.t2), ("Y", self.t2)])
        self.sigma2 = Substitution([("X", self.t2), ("Y", self.t3)])

    def testSubstBasic(self):
        """
        Test basic stuff.
        """
        tau = self.sigma1.copy()
        self.assertTrue(terms.termEqual(tau("X"), self.sigma1("X")))
        self.assertTrue(terms.termEqual(tau("Y"), self.sigma1("Y")))
        self.assertTrue(terms.termEqual(tau("Z"), self.sigma1("Z")))

        t = tau.modifyBinding(("X", self.t1))
        self.assertTrue(terms.termEqual(t, self.t2))
        t = tau.modifyBinding(("U", self.t1))
        self.assertEqual(t, None)
        self.assertTrue(tau.isBound("U"))
        self.assertTrue(terms.termEqual(tau.value("U"), self.t1))
        t = tau.modifyBinding(("U", None))
        self.assertTrue(not tau.isBound("U"))


    def testSubstApply(self):
        """
        Check application of substitutions
        """
        self.assertEqual(prover.clauses.conversion.term2String(self.sigma1(self.t1)), "f(a,g(a))")
        self.assertTrue(terms.termEqual(self.sigma1(self.t1), self.t4))
        self.assertTrue(terms.termEqual(self.sigma2(self.t1), self.t5))


    def testFreshVarSubst(self):
        """
        Test that
        """
        var1 = freshVar()
        var2 = freshVar()
        self.assertTrue(var1!=var2)

        vars = terms.termCollectVars(self.t1)
        sigma = freshVarSubst(vars)
        vars2 = terms.termCollectVars(sigma(self.t1))
        shared = set(vars).intersection(set(vars2))
        self.assertTrue(not shared)

    def testBacktrack(self):
        """
        Test backtrackable substitutions.
        """
        sigma = BTSubst()
        state = sigma.getState()
        sigma.addBinding(('X', string2Term("f(Y)")))
        res = sigma.backtrackToState(state)
        self.assertEqual(res, 1)
        res = sigma.backtrack()
        self.assertTrue(not res)

