#!/usr/bin/env python3
# ----------------------------------
#
# Module signature.py

"""
First-order signatures describe which names (for functions, including
constants, and predicates) are available in a given first-order
language. Very often, signatures are given implicitly. In other words,
the symbols used in terms and formulas implictly make up the
signature. For implementations of standard untyped predicate logic, we
can always extract the necessary information directly from the
formulae. 

However, for certain operations it is much easier to have an explicit
data object providing signature information. 

A signature is a triple (F,P,ar), with the following properties:

- F is a finite set of function symbols (including constants).
- P is a finite set of predicate symbols.
- F and P are disjunct, i.e. they don't share any symbols.
- ar:F \cup P ->N_0 is the  arity function that associates a natural
  number (the "arity") with each function symbol and predicate
  symbols.


Copyright 2012-2019 Stephan Schulz, schulz@eprover.org

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

class Signature(object):
    """
    A signature object, containing function symbols, predicate
    symbols, and their associated arities.
    """
    def __init__(self):
        """
        Initialize the signature.
        """
        self.funs  = {}
        self.preds = {}

    def __repr__(self):
        """
        Return a printable representation of the signture.
        """
        res = ["Predicates:\n-----------"]
        funs = [ "%s: %d"%(f, self.preds[f]) for f in self.preds.keys()]
        res.extend(funs)

        res.append("Functions:\n-----------")
        funs = [ "%s: %d"%(f, self.funs[f]) for f in self.funs.keys()]
        res.extend(funs)

        return "\n".join(res)

    def addFun(self, f, arity):
        """
        Add a function symbol with associated arity.
        """
        self.funs[f] = arity


    def addPred(self, p, arity):
        """
        Add a predicate symbol with associated arity.
        """
        self.preds[p] = arity

    def isPred(self, p):
        """
        Return True if p is a known predicate symbol.
        """
        return p in self.preds

    def isFun(self, f):
        """
        Return True if f is a known function symbol.
        """
        return f in self.funs

    def isConstant(self,f):
        """
        Return True if f is a constant function symbol.
        """
        return self.isFun(f) and self.getArity(f)==0

    def getArity(self, symbol):
        """
        Return the arity of a (known) symbol.
        """
        if self.isFun(symbol):
            return self.funs[symbol]
        return self.preds[symbol]



class TestSignature(unittest.TestCase):
    """
    Test basic functionality of the signature data type.
    """
    
    def testSig(self):
        """
        Test signature object.
        """
        sig = Signature()

        sig.addFun("mult", 2)
        sig.addFun("a", 0)
        sig.addPred("weird", 4)
        

        print(sig)
        self.assertTrue(sig.isPred("weird"))
        self.assertTrue(not sig.isPred("unknown"))
        self.assertTrue(not sig.isPred("a"))
        self.assertTrue(sig.isFun("a"))
        self.assertTrue(sig.isConstant("a"))
        self.assertTrue(not sig.isFun("unknown"))
        self.assertTrue(not sig.isFun("weird"))

        self.assertEqual(sig.getArity("a"),0)
        self.assertEqual(sig.getArity("weird"),4)


if __name__ == '__main__':
    unittest.main()
