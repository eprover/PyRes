#!/usr/bin/env python2.7
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

Since substitutions generated in matching are only simple collection
of individual bindings, we can simply backtrack to an earlier
state. This will become useful later, when we try to find a common
match for a small set of terms (or literals) onto any subset of a
larger set.


Copyright 2010-2011 Stephan Schulz, schulz@eprover.org

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
Hirschstrasse 35
76133 Karlsruhe
Germany
Email: schulz@eprover.org
"""

from terms import *
from substitutions import *




def match(t1, t2, subst):
    """
    Match t1 onto t2. If this succeeds, return true and modify subst
    accordingly. Otherwise, return false and leave subst unchanged
    (i.e. backtrack subst to the old state).
    """
    assert isinstance(subst, BTSubst)
    bt_state = subst.get_state()
    result = True
    mlist = [t1]
    tlist = [t2]
    while mlist:
       matcher  = mlist.pop()
       target   = tlist.pop()

       if termIsVar(matcher):
          if subst.is_bound(matcher):
             if not termEqual(subst.value(match), target):
                result = False
                break
             # No else case - variable is already bound correctly
          else:
             subst.add_binding((matcher, target))
       else:
          if termIsVar(target) or termFunc(matcher) != termFunc(target):
             result = False
             break
          else:
             mlist.extend(termArgs(matcher))
             tlist.extend(termArgs(target))
    if result:
       return True
    subst.backtrackToState(bt_state)
    return False
             
       


class TestMatching(unittest.TestCase):
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

    def match_test(self, s,t, success_expected):
       """
       Test if s can be matched onto t. If yes, report the
       result. Compare to the expected result.
       """
       print "Trying to match", term2String(s), "onto", term2String(t)
       sigma = BTSubst()
       res = match(s,t, sigma)
       if success_expected:
          self.assert_(res)
          self.assert_(termEqual(sigma(s), t))
          print term2String(sigma(s)), term2String(t), sigma
       else:
          print "Failure"
          self.assert_(not res)
       print

    def testMatch(self):
        """
        Test Matching.
        """
        print
        self.match_test(self.s1, self.t1, True)
        self.match_test(self.s2, self.t2, True)
        self.match_test(self.s3, self.t3, True)
        self.match_test(self.s4, self.t4, False)
        self.match_test(self.s5, self.t5, False)
        self.match_test(self.s6, self.t6, False)
        self.match_test(self.s7, self.t7, True)

        self.match_test(self.t1, self.s1, False)
        self.match_test(self.t2, self.s2, False)
        self.match_test(self.t3, self.s3, False)
        self.match_test(self.t4, self.s4, False)
        self.match_test(self.t5, self.s5, True)
        self.match_test(self.t6, self.s6, False)
        self.match_test(self.t7, self.s7, False)



if __name__ == '__main__':
    unittest.main()

