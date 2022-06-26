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

from prover.clauses.terms import *
from prover.proof.substitutions import *


def match(matcher, target, subst):
    """
    Match t1 onto t2. If this succeeds, return true and modify subst
    accordingly. Otherwise, return false and leave subst unchanged
    (i.e. backtrack subst to the old state). Providing a partial
    substitution allows us to use the function in places where we need
    to find a common match for several terms. 
    """
    assert isinstance(subst, BTSubst)
    bt_state = subst.getState()
    result = True

    if termIsVar(matcher):
        if subst.isBound(matcher):
            if not termEqual(subst.value(matcher), target):
                result = False
            # No else case - variable is already bound correctly
        else:
            subst.addBinding((matcher, target))
    else:
        if termIsVar(target) or termFunc(matcher) != termFunc(target):
            result = False
        else:
            for (s, t) in zip(termArgs(matcher), termArgs(target)):
                result = match(s, t, subst)
                if not result:
                    break
    if result:
        return True
    subst.backtrackToState(bt_state)
    return False


def match_norec(t1, t2, subst):
    """
    Match t1 onto t2. If this succeeds, return true and modify subst
    accordingly. Otherwise, return false and leave subst unchanged
    (i.e. backtrack subst to the old state). Providing a partial
    substitution allows us to use the function in places where we need
    to find a common match for several terms. This is an alternative
    implementation using explicit work lists instead of recursion.
    """
    assert isinstance(subst, BTSubst)
    bt_state = subst.getState()
    result = True
    mlist = [t1]
    tlist = [t2]
    while mlist:
        matcher = mlist.pop()
        target = tlist.pop()

        if termIsVar(matcher):
            if subst.isBound(matcher):
                if not termEqual(subst.value(matcher), target):
                    result = False
                    break
                # No else case - variable is already bound correctly
            else:
                subst.addBinding((matcher, target))
        else:
            if termIsVar(target) or termFunc(matcher) != termFunc(target):
                result = False
                break
            else:
                # We now know that matcher is of the form f(s1, ..., sn)
                # and target is of the form f(t1, ..., tn). So now we
                # need to find a common substitution for s1 onto t1,
                # ..., sn onto tn. To do this, we add the argument lists
                # to the work lists and let them be processed in the same
                # loop.
                mlist.extend(termArgs(matcher))
                tlist.extend(termArgs(target))
    if result:
        return True
    subst.backtrackToState(bt_state)
    return False
