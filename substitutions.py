#!/usr/bin/env python2.7
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

import terms
import unittest


class Substitution(object):
    """
    Substitutions map variables to terms. Substitutions as used here
    are always fully expanded, i.e. each variable is bound directly to
    the term it maps too.
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
        Return the value assigned to a variable.
        """
        if var in self.subst:
            return self.subst[var]
        else:
            return var

    def apply(self, term):
        """
        Apply the substitution to a term. Return the result.
        """
        if terms.termIsVar(term):
            return self.value(term)
        else:
            res  = [term[0]]
            args = map(lambda x:self.apply(x), terms.termArgs(term))
            res.extend(args)
            return res                      
        
    def add_binding(self, var, term):
        """
        Add a new binding to a substitution. 
        """
        tmpsubst = Substitution([(var, term)])
        vars = self.subst.keys()
        for x in vars:
            bound = self.subst[x]
            self.subst[x] = tmpsubst.apply(bound)
        if not var in self.subst:
            self.subst[var] = term



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
        tau = self. sigma1.copy()
        self.assert_(terms.termEqual(tau("X"), self.sigma1("X")))
        self.assert_(terms.termEqual(tau("Y"), self.sigma1("Y")))
        self.assert_(terms.termEqual(tau("Z"), self.sigma1("Z")))
        
        
    def testSubstApply(self):
        """
        Check application of substitutions
        """
        self.assertEqual(terms.term2String(self.sigma1(self.t1)),"f(a,g(a))")
        self.assert_(terms.termEqual(self.sigma1(self.t1),  self.t4))
        self.assert_(terms.termEqual(self.sigma2(self.t1),  self.t5))


if __name__ == '__main__':
    unittest.main()
