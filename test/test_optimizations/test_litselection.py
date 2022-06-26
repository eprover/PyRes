"""
Copyright 2019 Stephan Schulz, schulz@eprover.org

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

from prover.optimizations.litselection import *
from prover.parser.lexer import Lexer
from prover.parser.parser import parseLiteralList


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
        lit = ll[0]
        self.assertEqual(lit, l1)

        ll = smallestLit(ll1)
        self.assertEqual(len(ll), 1)
        lit = ll[0]
        self.assertEqual(lit, l1)

        ll = largestLit(ll1)
        self.assertEqual(len(ll), 1)
        lit = ll[0]
        self.assertEqual(lit, l2)

        ll = varSizeLit(ll1)
        self.assertEqual(len(ll), 1)
        lit = ll[0]
        self.assertEqual(lit, l4)

        ll = eqResVarSizeLit(ll1)
        self.assertEqual(len(ll), 1)
        lit = ll[0]
        self.assertEqual(lit, l3)

        lex = Lexer(self.str2)
        ll1 = parseLiteralList(lex)
        l1, l2, l3 = ll1
        ll = eqResVarSizeLit(ll1)
        self.assertEqual(len(ll), 1)
        lit = ll[0]
        self.assertEqual(lit, l3)
