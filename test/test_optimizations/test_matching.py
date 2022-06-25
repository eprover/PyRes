#!/usr/bin/env python3
# ----------------------------------
#
# Module matching.py

"""
This code implements matching for first-order terms
(and, by inheritance, atoms).


=== Matching ===

Matching s onto t is the process of trying to find a substitution
sigma such that sigma(s)=t. Note that the substitution is only applied
to one term (the "potentially more general term"). This simple change
makes matching a much easier process than unification. No occurs check
is necessary, and each variable needs to be bound at most once, to a
single fixed and unchanging term. As a result, we don't need to
compose substitutions, and we don't need to apply substitutions - we
simply go through both terms in any reasonable order, collect simple
variable bindings if a variable in s coincides with a term in t, and
determine a conflict if either the terms are structurally
incompatible, or if a variable in s would need to be bound to two
different terms.

Examples:

X  matches f(X)  with sigma = {X <- f(X)}
   Note that X and f(X) cannot be unified because of the
   occurs-check. However, in matching, the substitution is only
   applied to one side.

X matches X     with sigma = {}
   However, in this case we might want  to record the binding X<-X
   explicitly, because if we want to extend the match to further
   terms, we cannot rebind X

f(X,a) does not match f(a,X)
   The two terms are unifiable, but again, in matching the
   substitution is only applied to the potentially matching term.

Since substitutions generated in matching are only simple collection
of individual bindings, we can simply backtrack to an earlier
state. This will become useful later, when we try to find a common
match for a small set of terms (or literals) onto any subset of a
larger set.


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

from prover.optimizations.matching import *
from prover.clauses.terms import string2Term, term2String, termEqual
from prover.proof.substitutions import BTSubst


class TestMatching(unittest.TestCase):
    """
    Test basic substitution functions.
    """

    def setUp(self):
        self.s1 = string2Term("X")
        self.t1 = string2Term("a")

        self.s2 = string2Term("X")
        self.t2 = string2Term("f(X)")

        self.s3 = string2Term("X")
        self.t3 = string2Term("f(Y)")

        self.s4 = string2Term("f(X, a)")
        self.t4 = string2Term("f(b, Y)")

        self.s5 = string2Term("f(X, g(a))")
        self.t5 = string2Term("f(X, Y))")

        self.s6 = string2Term("f(X, g(a))")
        self.t6 = string2Term("f(X, X))")

        self.s7 = string2Term("g(X)")
        self.t7 = string2Term("g(f(g(X),b))")

    def match_test(self, match, s, t, success_expected):
        """
       Test if s can be matched onto t. If yes, report the
       result. Compare to the expected result.
       """
        print("Trying to match", term2String(s), "onto", term2String(t))
        sigma = BTSubst()
        res = match(s, t, sigma)
        if success_expected:
            self.assertTrue(res)
            self.assertTrue(termEqual(sigma(s), t))
            print(term2String(sigma(s)), term2String(t), sigma)
        else:
            print("Failure")
            self.assertTrue(not res)
        print()

    def testMatch(self):
        """
        Test Matching.
        """
        print()
        self.match_test(match, self.s1, self.t1, True)
        self.match_test(match, self.s2, self.t2, True)
        self.match_test(match, self.s3, self.t3, True)
        self.match_test(match, self.s4, self.t4, False)
        self.match_test(match, self.s5, self.t5, False)
        self.match_test(match, self.s6, self.t6, False)
        self.match_test(match, self.s7, self.t7, True)

        self.match_test(match, self.t1, self.s1, False)
        self.match_test(match, self.t2, self.s2, False)
        self.match_test(match, self.t3, self.s3, False)
        self.match_test(match, self.t4, self.s4, False)
        self.match_test(match, self.t5, self.s5, True)
        self.match_test(match, self.t6, self.s6, False)
        self.match_test(match, self.t7, self.s7, False)

        self.match_test(match, self.t6, self.t6, True)

    def testMatchNoRec(self):
        """
        Test Matching.
        """
        print()
        self.match_test(match_norec, self.s1, self.t1, True)
        self.match_test(match_norec, self.s2, self.t2, True)
        self.match_test(match_norec, self.s3, self.t3, True)
        self.match_test(match_norec, self.s4, self.t4, False)
        self.match_test(match_norec, self.s5, self.t5, False)
        self.match_test(match_norec, self.s6, self.t6, False)
        self.match_test(match_norec, self.s7, self.t7, True)

        self.match_test(match_norec, self.t1, self.s1, False)
        self.match_test(match_norec, self.t2, self.s2, False)
        self.match_test(match_norec, self.t3, self.s3, False)
        self.match_test(match_norec, self.t4, self.s4, False)
        self.match_test(match_norec, self.t5, self.s5, True)
        self.match_test(match_norec, self.t6, self.s6, False)
        self.match_test(match_norec, self.t7, self.s7, False)

        self.match_test(match_norec, self.t6, self.t6, True)


if __name__ == '__main__':
    unittest.main()
