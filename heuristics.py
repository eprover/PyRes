#!/usr/bin/env python2.7
# ----------------------------------
#
# Module heuristics.py

"""
This module implements heuristical evaluation functions for clauses. A
heuristical evaluation function is a function h:Clauses(F,P,X)->R
(where R denotes the set of real numbers, or, in the actual
implementation, the set of floating point numbers).

A lower value of h(C) for some clause C implies that C is assumed to
be better (or more useful) in a given proof search, and should be
processed before a clause C' with larger value h(C').

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

import unittest
from lexer import Lexer
import clauses


class ClauseEvaluationFunction(object):
    """
    A class representing a clause evaluation function. This is a pure
    virtual class, and it really is just a wrapper around the given
    clause evaluation function. However, some heuristics may need
    to be able to store information, either from initialization, or
    from previous calls.
    """
        
    def __init__(self): # pragma: nocover
        """
        Initialize the evaluaton function.
        """
        self.name = "Virtual Base"
        
    def __repr__(self): # pragma: nocover
        """
        Return a string representation of the clause.
        """
        return "ClauseEvalFun(%s)"%(self.name,)

    def __call__(self, clause): 
        """
        Provide this as a callable function.
        """
        return self.hEval(clause)
   
    def hEval(self, clause): # pragma: nocover
        """
        This needs to be overloaded...
        """
        assert False and "Virtual base class is not callable"
        

class FIFOEvaluation(ClauseEvaluationFunction):
    """
    Class implementing first-in-first-out evaluation - i.e. clause
    evalutations increase over time (and independent of the clause).
    """
    def __init__(self):
        """
        Initialize object.
        """
        self.name        = "FIFOEval"
        self.fifocounter = 0

    def hEval(self, clause):
        """
        Actual evaluation function.
        """
        self.fifocounter = self.fifocounter + 1
        return self.fifocounter


class SymbolCountEvaluation(ClauseEvaluationFunction):
    """
    Implement a standard symbol counting heuristic. 
    """
    def __init__(self, fweight=2, vweight=1):
        """
        Initialize heuristic.
        """
        self.fweight = fweight
        self.vweight = vweight
        self.name    = "SymbolCountEval(%f,%f)"%(fweight,vweight)

    def hEval(self, clause):
        """
        Actual evaluation function.
        """
        return clause.weight(self.fweight, self.vweight)

        

class TestHeuristics(unittest.TestCase):
    """
    Test heuristic evaluation functions.
    """
    def setUp(self):
        """
        Setup function for tests. Create some clauses to test
        evaluations on.
        """
        print
        self.spec ="""
cnf(c1,axiom,(f(X1,X2)=f(X2,X1))).
cnf(c2,axiom,(f(X1,f(X2,X3))=f(f(X1,X2),X3))).
cnf(c3,axiom,(g(X1,X2)=g(X2,X1))).
cnf(c4,axiom,(f(f(X1,X2),f(X3,g(X4,X5)))!=f(f(g(X4,X5),X3),f(X2,X1))|k(X1,X1)!=k(a,b))).
cnf(c5,axiom,(b=c|X1!=X2|X3!=X4|c!=d)).
cnf(c6,axiom,(a=b|a=c)).
cnf(c7,axiom,(i(X1)=i(X2))).
cnf(c8,axiom,(c=d|h(i(a))!=h(i(e)))).
"""
        lexer = Lexer(self.spec)
        self.c1 = clauses.parseClause(lexer)
        self.c2 = clauses.parseClause(lexer)
        self.c3 = clauses.parseClause(lexer)
        self.c4 = clauses.parseClause(lexer)
        self.c5 = clauses.parseClause(lexer)
        self.c6 = clauses.parseClause(lexer)
        self.c7 = clauses.parseClause(lexer)
        self.c8 = clauses.parseClause(lexer)
        

    def testFIFO(self):
        """
        Test that basic literal parsing works correctly.
        """
        eval = FIFOEvaluation()
        e1 = eval(self.c1)
        e2 = eval(self.c2)
        e3 = eval(self.c3)
        e4 = eval(self.c4)
        e5 = eval(self.c5)
        e6 = eval(self.c6)
        e7 = eval(self.c7)
        e8 = eval(self.c8)
        self.assert_(e1<e2)
        self.assert_(e2<e3)
        self.assert_(e3<e4)
        self.assert_(e4<e5)
        self.assert_(e5<e6)
        self.assert_(e6<e7)
        self.assert_(e7<e8)

    def testSymbolCount(self):
        """
        Test that basic literal parsing works correctly.
        """
        eval = SymbolCountEvaluation(2,1)
        e1 = eval(self.c1)
        e2 = eval(self.c2)
        e3 = eval(self.c3)
        e4 = eval(self.c4)
        e5 = eval(self.c5)
        e6 = eval(self.c6)
        e7 = eval(self.c7)
        e8 = eval(self.c8)
        self.assertEqual(e1, self.c1.weight(2,1))
        self.assertEqual(e2, self.c2.weight(2,1))
        self.assertEqual(e3, self.c3.weight(2,1))
        self.assertEqual(e4, self.c4.weight(2,1))
        self.assertEqual(e5, self.c5.weight(2,1))
        self.assertEqual(e6, self.c6.weight(2,1))
        self.assertEqual(e7, self.c7.weight(2,1))
        self.assertEqual(e8, self.c8.weight(2,1))
      

if __name__ == '__main__':
    unittest.main()
