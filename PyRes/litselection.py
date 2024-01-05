#!/usr/bin/env python3
# ----------------------------------
#
# Module litselection.py

"""
Functions supporting (negative) literal selection. Literal selection
indicates certain literals of a clause as "inference literals", and
only allows factoring, if at least one of the involved literals is an
inference literal, and resolution, if both involved literals are
inference literals.

Literal selection reduces the number of possible inferences, and hence
the explosion of the search space. The resolution calculus with
literal selection remains complete, if the literal selection function
has certain properties. One sufficient condition is formulated as
follows ("negative literal selection"):

   In a clause, either at least one negatve literal is selected, or
   all literals are selected.

Intuitively, this can be explained as follows: A clause -a1 v -a2 v a3
v a4 can be read as a conditional statement: (a1 ^ a2)->(a3 v a4). In
other words, the negative literals are seen as conditions that must be
met to be able to deduce the disjunction of positive
literals. In that case, all conditions must be resolved. Negative
literal selection simply imposes an arbitrary order on the solution of
this condition.

Much of the mechanism of literal selection has been implemented in
literals.py and rescontrol.py. This module implements function that
select a given subset of inference literals from a list of negative
literals.

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
from lexer import Token,Lexer
from literals import Literal, parseLiteral, parseLiteralList,\
     literalList2String


def firstLit(litlist):
    """
    Return the first element of the list (as a sublist).
    """
    assert(litlist)
    return litlist[0:1]

def smallestLit(litlist):
    """
    Return the smallest element of the list (as a sublist).
    """
    assert(litlist)
    litlist.sort(key=lambda x:x.weight(1,1))
    return litlist[0:1]

def largestLit(litlist):
    """
    Return the largest element of the list (as a sublist).
    """
    assert(litlist)
    litlist.sort(key=lambda x:x.weight(1,1))
    return [litlist[-1]]


def varSizeEval(lit):
    """
    Return a tuple <number of vars, weight>.
    """
    return (len(lit.collectVars()), -lit.weight(1,1))

def varSizeLit(litlist):
    """
    Return the largest literal among those with the smallest
    variable list.
    """
    assert(litlist)
    litlist.sort(key=varSizeEval)
    return litlist[0:1]


def eqResVarSizeLit(litlist):
    """
    Return the first literal of the form X=Y, or the largest literal
    among those with the smallest variable set if no pure variable
    literal exists.
    """
    assert(litlist)
    for l in litlist:
        if l.isPureVarLit():
            return [l]

    litlist.sort(key=varSizeEval)
    return litlist[0:1]



LiteralSelectors = {
    "first" : firstLit,
    "smallest" : smallestLit,
    "largest" : largestLit,
    "leastvars" : varSizeLit,
    "eqleastvars" : eqResVarSizeLit
    }
"""
Table associating name and selection function, so that we can select
the function by name.
"""




class TestLitSelection(unittest.TestCase):
    """
    Unit test class for literal selection.
    """
    def setUp(self):
        """
        Setup function for literal selection.
        """
        print()
        self.str1 = """
        ~p(a)|~p(f(X,g(a)))|X!=Y|~q(a,g(a))
"""
        self.str2 = """
        ~p(a)|~p(f(X,g(a)))|~q(a,g(a))
"""

    def testClauses(self):
        """
        Test that basic literal parsing works correctly.
        """
        lex = Lexer(self.str1)
        ll1 = parseLiteralList(lex)
        l1, l2, l3, l4 = ll1

        ll = firstLit(ll1)
        self.assertEqual(len(ll), 1)
        l = ll[0]
        self.assertEqual(l, l1)

        ll = smallestLit(ll1)
        self.assertEqual(len(ll), 1)
        l = ll[0]
        self.assertEqual(l, l1)

        ll = largestLit(ll1)
        self.assertEqual(len(ll), 1)
        l = ll[0]
        self.assertEqual(l, l2)

        ll = varSizeLit(ll1)
        self.assertEqual(len(ll), 1)
        l = ll[0]
        self.assertEqual(l, l4)

        ll = eqResVarSizeLit(ll1)
        self.assertEqual(len(ll), 1)
        l = ll[0]
        self.assertEqual(l, l3)

        lex = Lexer(self.str2)
        ll1 = parseLiteralList(lex)
        l1, l2, l3 = ll1
        ll = eqResVarSizeLit(ll1)
        self.assertEqual(len(ll), 1)
        l = ll[0]
        self.assertEqual(l, l3)





if __name__ == '__main__':
    unittest.main()
