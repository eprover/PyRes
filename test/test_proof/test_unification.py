#!/usr/bin/env python3
# ----------------------------------
#
# Module unification.py

"""
This code implements unification for first-order terms (and, by
inheritance, atoms).


=== Unification ===

The goal of a unification algorithm is to find a substitution sigma
that will make two term s and t equal, i.e. sigma(s)=sigma(t).  The
unification algorithm we implement here is based on simultaneous
solution of sets of equations over terms. It operates on a tuple with
two elements: A set of equations and a substitution.

The initial tuple for unifying s and t is
{s=t}, {}
i.e. it consists of the single equation s=t and the empty
substitution. The goal is to step by step build a substitution that
will make s and t equal.

The unification algorithm picks an arbitray equation and tries to
handle it by one of the following rules. It terminates either when the
set of equations is empty (in that case the resulting substitution is
the most general unifier), or if it derives FAIL, in which case the
two original terms are not unifiable.

The "Bind" rules handle the case that one of the two terms of the
given equation is a variable X. If X does not occur in the
other term t, the rule binds t to X, applies this binding to the open
equations, and records it in sigma.


Bind 1
{X=t} \cup R, sigma
========================= if X does not occur in t
{X<-t}(R), sigma \circ {X<-t}

Bind 2
{t=X} \cup R, sigma
=========================  if X does not occur in t
{X<-t}(R), sigma \circ {X<-t}


The "Decompose" rule handles two terms with the same top function
symbol. Since this symbol is already equal, we just need to make the
individual argument terms equal. This is reflected by creating a new
equation for each pair of corresponding arguments, and adding them to
the list of open equations.


Decompose:
{f(s1, ..., sn)=f(t1, ..., tn)} \cup R, sigma
==============================================
{s1=t1, ..., sn=tn} \cup R, sigma


A trivial case easily overlooked is the case of an equation between
two variables that are already equal:


Solved:
{X=X} \cup R, sigma
=========================
R, sigma


If none of the above rules is applicable, then we cannot solve the
given equation with a substitution. We can recognize these cases and
transition to an explixit failure state.

In the first failure case, the top function symbols of the two terms
clash. Since the application of a substitution never changes a
function symbol, no substitution can make the two terms equal.


Structural fail:
{f(s1, ..., tn) = g(t1, ..., tm) \cup R, sigma
=============================================== if f!=g
FAIL


The second cause of failure is an equation where a variable X on one
side has to be unified with a term t[X] that contains the same
variable embedded on the other side. No binding of X will ever get rid
of the context in which X is embedded, so no substitution will ever
make X and t[X] equal.


Occurs-Fail 1:
{X=t} \cup R, sigma
==================== if X does occur in t, X!=t
FAIL


Occurs-Fail 2:
{t=X} \cup R, sigma
====================  if X does occur in t, X!=t
FAIL



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
