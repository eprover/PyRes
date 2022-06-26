#!/usr/bin/env python3
# ----------------------------------
#
# Module terms.py

"""
Copyright 2010-2019 Stephan Schulz, schulz@eprover.org

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
from prover.clauses.terms import *


class TestTerms(unittest.TestCase):
    """
    Test basic term functions.
    """

    def setUp(self):
        self.example1 = "X"
        self.example2 = "a"
        self.example3 = "g(a,b)"
        self.example4 = "g(X, f(Y))"
        self.example5 = "g(X, f(Y))"
        self.example6 = "g(b,b)"
        self.example7 = "'g'(b,b)"
        self.example8 = "g(X, f(X))"
        self.t1 = string2Term(self.example1)
        self.t2 = string2Term(self.example2)
        self.t3 = string2Term(self.example3)
        self.t4 = string2Term(self.example4)
        self.t5 = string2Term(self.example5)
        self.t6 = string2Term(self.example6)
        self.t7 = string2Term(self.example7)
        self.t8 = string2Term(self.example8)

    def testToString(self):
        """
        Test that stringTerm and term2String are dual. Start with
        terms, so that we are sure to get the canonical string
        representation.
        """
        self.assertEqual(string2Term(term2String(self.t1)), self.t1)
        self.assertEqual(string2Term(term2String(self.t2)), self.t2)
        self.assertEqual(string2Term(term2String(self.t3)), self.t3)
        self.assertEqual(string2Term(term2String(self.t4)), self.t4)
        self.assertEqual(string2Term(term2String(self.t7)), self.t7)

    def testIsVar(self):
        """
        Test if the classification function work as expected.
        """
        self.assertTrue(termIsVar(self.t1))
        self.assertTrue(not termIsVar(self.t2))
        self.assertTrue(not termIsVar(self.t3))
        self.assertTrue(not termIsVar(self.t4))

    def testIsCompound(self):
        """
        Test if the classification function work as expected.
        """
        self.assertTrue(not termIsCompound(self.t1))
        self.assertTrue(termIsCompound(self.t2))
        self.assertTrue(termIsCompound(self.t3))
        self.assertTrue(termIsCompound(self.t4))

    def testEquality(self):
        """
        Test if term equality works as expected.
        """
        self.assertTrue(termEqual(self.t1, self.t1))
        self.assertTrue(termEqual(self.t2, self.t2))
        self.assertTrue(termEqual(self.t3, self.t3))
        self.assertTrue(termEqual(self.t4, self.t4))
        self.assertTrue(termEqual(self.t5, self.t5))

        self.assertTrue(termEqual(self.t4, self.t5))

        self.assertTrue(not termEqual(self.t1, self.t4))
        self.assertTrue(not termEqual(self.t3, self.t4))
        self.assertTrue(not termEqual(self.t3, self.t6))

        l1 = []
        l2 = [self.t1]
        self.assertTrue(not termListEqual(l1, l2))

    def testCopy(self):
        """
        Test if term copying works.
        """
        t1 = termCopy(self.t1)
        self.assertTrue(termEqual(t1, self.t1))
        t2 = termCopy(self.t2)
        self.assertTrue(termEqual(t2, self.t2))
        t3 = termCopy(self.t3)
        self.assertTrue(termEqual(t3, self.t3))
        t4 = termCopy(self.t4)
        self.assertTrue(termEqual(t4, self.t4))

    def testIsGround(self):
        """
        Test if isGround() works as expected.
        """
        self.assertTrue(not termIsGround(self.t1))
        self.assertTrue(termIsGround(self.t2))
        self.assertTrue(termIsGround(self.t3))
        self.assertTrue(not termIsGround(self.t4))
        self.assertTrue(not termIsGround(self.t5))

    def testCollectVars(self):
        """
        Test the variable collection.
        """
        vars = termCollectVars(self.t1)
        self.assertEqual(len(vars), 1)
        termCollectVars(self.t2, vars)
        self.assertEqual(len(vars), 1)
        termCollectVars(self.t3, vars)
        self.assertEqual(len(vars), 1)
        termCollectVars(self.t4, vars)
        self.assertEqual(len(vars), 2)
        termCollectVars(self.t5, vars)
        self.assertEqual(len(vars), 2)

        self.assertTrue("X" in vars)
        self.assertTrue("Y" in vars)

    def testCollectFuns(self):
        """
        Test function symbol collection.
        """
        funs = termCollectFuns(self.t1)
        self.assertEqual(funs, set())

        funs = termCollectFuns(self.t2)
        self.assertEqual(funs, {"a"})

        funs = termCollectFuns(self.t3)
        self.assertEqual(funs, {"g", "a", "b"})

        funs = termCollectFuns(self.t4)
        self.assertEqual(funs, {"g", "f"})

        funs = termCollectFuns(self.t5)
        self.assertEqual(funs, {"g", "f"})

        funs = termCollectFuns(self.t6)
        self.assertEqual(funs, {"g", "b"})

    def testCollectSig(self):
        """
        Test signature collection.
        """
        sig = termCollectSig(self.t1)
        sig = termCollectSig(self.t2, sig)
        sig = termCollectSig(self.t3, sig)
        sig = termCollectSig(self.t4, sig)
        sig = termCollectSig(self.t5, sig)
        sig = termCollectSig(self.t6, sig)

        self.assertEqual(sig.getArity("f"), 1)
        self.assertEqual(sig.getArity("g"), 2)
        self.assertEqual(sig.getArity("a"), 0)
        self.assertEqual(sig.getArity("b"), 0)

    def testWeight(self):
        """
        Test if termWeight() works as expected.
        """
        self.assertTrue(termWeight(self.t1, 1, 2) == 2)
        self.assertTrue(termWeight(self.t2, 1, 2) == 1)
        self.assertTrue(termWeight(self.t3, 1, 2) == 3)
        self.assertTrue(termWeight(self.t4, 1, 2) == 6)
        self.assertTrue(termWeight(self.t5, 2, 1) == 6)

    def testSubterm(self):
        """
        Test if subterm() works as expected.
        self.example5 = "g(X, f(Y))"
        """
        self.assertTrue(subterm(self.t5, []) == ['g', 'X', ['f', 'Y']])
        self.assertTrue(subterm(self.t5, [0]) == 'g')
        self.assertTrue(subterm(self.t5, [1]) == 'X')
        self.assertTrue(subterm(self.t5, [2, 0]) == 'f')
        self.assertTrue(subterm(self.t5, [5, 0]) is None)

    def testTermIsSubterm(self):
        """
        Test if termIsSubterm() works as expected.
        """
        self.assertTrue((termIsSubterm(self.t5, subterm(self.t5, [0]))) is True)
        self.assertTrue((termIsSubterm(self.t5, self.t5)) is True)
        self.assertTrue((termIsSubterm(subterm(self.t5, [0]), self.t5)) is False)
        self.assertTrue((termIsSubterm(self.t5, self.t2)) is False)

    def testCountVarOccurences(self):
        """
        Test if getvaroccurences() works as expected.
        """
        self.assertTrue(countvaroccurrences(self.t1, 1).keys() == {"X"})
        self.assertTrue(countvaroccurrences(self.t1, 1).get("X") == 1)
        self.assertTrue(countvaroccurrences(self.t1, -1).get("X") == -1)
        self.assertTrue(countvaroccurrences(self.t4, 1).keys() == {"X", "Y"})
        self.assertTrue(countvaroccurrences(self.t4, 1).get("X") == 1)
        self.assertTrue(countvaroccurrences(self.t4, 1).get("Y") == 1)
        self.assertTrue(countvaroccurrences(self.t8, 1).get("X") == 2)


if __name__ == '__main__':
    unittest.main()
