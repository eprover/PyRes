#!/usr/bin/env python3
# ----------------------------------
#
# Module substitutions.py

"""
A simple implementation of substitutions.

Definition: A substitution sigma is a function sigma:V->Terms(F,V)
with the property that sigma(X)=X for all but finitely many variables
X from V.

A substitution is continued to terms recursively:
sigma(f(t1, ..., tn)) = f(sigma(t1), ..., sigma(t2))

Substitutions are customarily represented by the Greek letter simga.

Footnote:
If more than one substitution is needed, the second one is usually
called tau, and further ones are denoted with primes or subscripts.

We represent substitutions by a thin wrapper around Python
dictionaries mapping variables to terms.

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

import terms
import unittest


class Substitution(object):
    """
    Substitutions map variables to terms. Substitutions as used here
    are always fully expanded, i.e. each variable is bound directly to
    the term it maps to.
    """

    varCounter = 1
    """
    A counter to generate fresh variables.
    """

    def __init__(self, init = []):
        """
        Initialize. The optional argument is a list of variable/term
        pairs representing the initial binding. This is taken as-is,
        without any checks for consistency.
        """
        self.subst = {}
        for i in init:
            self.subst[i[0]]=i[1]

    def __repr__(self):
        """
        Return a print representation of the substitution.
        """
        return "{"+\
               ",".join([i+"<-"+terms.term2String(self.subst[i])
                         for i in self.subst])\
                         +"}"

    def __call__(self, term):
        """
        Pretty synonym for apply() allowing us to use substitutions as
        functions.
        """
        return self.apply(term)

    def copy(self):
        """
        Return a (flat) copy of the substitution.
        """
        res = Substitution()
        res.subst = dict(self.subst)
        return res

    def value(self, var):
        """
        Return the value of a variable (i.e. the term it is bound to,
        or the variable itself if it is not bound).
        """
        if var in self.subst:
            return self.subst[var]
        else:
            return var

    def isBound(self, var):
        """
        Return True if var is bound in self, false otherwise.
        """
        return var in self.subst

    def apply(self, term):
        """
        Apply the substitution to a term. Return the result.
        """
        if terms.termIsVar(term):
            return self.value(term)
        else:
            res  = [term[0]]
            args = [self.apply(x) for x in terms.termArgs(term)]
            res.extend(args)
            return res

    def modifyBinding(self, binding):
        """
        Modify the substitution by adding a new binding (var,
        term). If the term is None, remove any binding for var. If it
        is not, add the binding. In either case, return the previous
        binding of the variable, or None if it was unbound.
        """
        var, term = binding
        if self.isBound(var):
            res = self.value(var)
        else:
            res = None

        if term == None:
            if self.isBound(var):
                del self.subst[var]
        else:
            self.subst[var] = term

        return res

    def composeBinding(self, binding):
        """
        Compose a new binding to an existing substitution.
        """
        tmpsubst = Substitution([binding])
        var, term = binding
        vars = self.subst.keys()
        for x in vars:
            bound = self.subst[x]
            self.subst[x] = tmpsubst.apply(bound)
        if not var in self.subst:
            self.subst[var] = term



class BTSubst(Substitution):
   """
   A substitution that does not allow composition of new bindings, but
   in exchange offers backtrackability. Bindings are recorded in two
   data structures:
   self.subst is a dictionary that maps variables to terms
   self.bindings is an ordered list of bindings.
   """
   def __init__(self, init = []):
      """
      Initialize. The optional argument is a list of variable/term
      pairs representing the initial binding. This is taken as-is,
      without any checks for consistency.
      """
      self.bindings = list(init)
      Substitution.__init__(self, init)

   def getState(self):
      """
      Return a state to which this substitution can be backtracked
      later. We encode the state of the binding list, but also the
      object itself, to allow for some basic sanity checking.
      """
      return (self, len(self.bindings))

   def backtrack(self):
      """
      Backtrack a single binding (if there is one). Return success or
      failure.
      """
      if self.bindings:
         tmp = self.bindings.pop()
         del self.subst[tmp[0]]
         return True
      else:
         return False

   def backtrackToState(self, bt_state):
      """
      Backtrack to the given state. Note that we only perform very
      basic sanity checking. Return number of binding retracted.
      """
      subst, state = bt_state
      assert subst == self
      res = 0

      while len(self.bindings)>state:
         self.backtrack()
         res = res+1
      return res

   def addBinding(self, binding):
      """
      Add a single binding to the substitution.
      """
      var, term = binding
      self.subst[var] = term
      self.bindings.append(binding)

   def composeBinding(self, binding): # pragma: no cover
      """
      Overloaded to catch usage errors!
      """
      assert False and \
             "You cannot compose backtrackable substitutions."


def freshVar():
    """
    Return a fresh variable. Note that this is not guaranteed to be
    different from input variables. However, it is guaranteed that
    freshVar() will never return the same variable more than once.
    """
    Substitution.varCounter += 1
    return "X%d"%(Substitution.varCounter,)


def freshVarSubst(vars):
    """
    Create a substitution that maps all variables in the list vars to
    fresh variables. Note that there is no guarantee that the fresh
    variables have never been used. However, there is a a guarantee
    that the fresh variables have never been produced by a uniqSubst
    substitution.

    """
    l = [(var, freshVar()) for var in vars]
    return Substitution(l)




class TestSubst(unittest.TestCase):
    """
    Test basic substitution functions.
    """
    def setUp(self):
        self.t1 = terms.string2Term("f(X, g(Y))")
        self.t2 = terms.string2Term("a")
        self.t3 = terms.string2Term("b")
        self.t4 = terms.string2Term("f(a, g(a))")
        self.t5 = terms.string2Term("f(a, g(b))")

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
        self.assertEqual(terms.term2String(self.sigma1(self.t1)),"f(a,g(a))")
        self.assertTrue(terms.termEqual(self.sigma1(self.t1),  self.t4))
        self.assertTrue(terms.termEqual(self.sigma2(self.t1),  self.t5))


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
        sigma.addBinding(('X', terms.string2Term("f(Y)")))
        res = sigma.backtrackToState(state)
        self.assertEqual(res, 1)
        res = sigma.backtrack()
        self.assertTrue(not res)



if __name__ == '__main__':
    unittest.main()
