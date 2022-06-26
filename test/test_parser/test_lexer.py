#!/usr/bin/env python3
# ----------------------------------
#
# Module lexer.py

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
from prover.parser.lexer import Lexer, Token, IllegalCharacterError, UnexpectedTokenError, UnexpectedIdentError


class TestLexer(unittest.TestCase):
    """
    Test the lexer functions.
    """

    def setUp(self):
        print()
        self.example1 = "f(X,g(a,b))"
        self.example2 = "# Comment\nf(X,g(a,b))"
        self.example3 = "cnf(test,axiom,p(a)|p(f(X)))."
        self.example4 = "^"
        self.example5 = "fof(test,axiom,![X,Y]:?[Z]:~p(X,Y,Z))."

    def testLex(self):
        """
        Test that comments and whitespace are normally ignored.
        """
        lex1 = Lexer(self.example1)
        lex2 = Lexer(self.example2)
        res1 = [(i.type, i.literal) for i in lex1.Lex()]
        res2 = [(i.type, i.literal) for i in lex2.Lex()]
        self.assertEqual(res1, res2)

    def testTerm(self):
        """
        Test that self.example 1 is split into the expected tokens.
        """
        lex1 = Lexer(self.example1)
        lex1.AcceptTok([Token.IdentLower])  # f
        lex1.AcceptTok([Token.OpenPar])  # (
        lex1.AcceptTok([Token.IdentUpper])  # X
        lex1.AcceptTok([Token.Comma])  # ,
        lex1.AcceptTok([Token.IdentLower])  # g
        lex1.AcceptTok([Token.OpenPar])  # (
        lex1.AcceptTok([Token.IdentLower])  # a
        lex1.AcceptTok([Token.Comma])  # ,
        lex1.AcceptTok([Token.IdentLower])  # b
        lex1.AcceptTok([Token.ClosePar])  # )
        lex1.AcceptTok([Token.ClosePar])  # )

    def testClause(self):
        """
        Perform lexical analysis of a clause, then rebuild it and
        compare that the strings are the same.
        """
        lex = Lexer(self.example3)
        toks = lex.Lex()
        print(toks)
        self.assertEqual(len(toks), 20)
        tmp = [i.literal for i in toks]
        rebuild = "".join([i.literal for i in toks])
        self.assertEqual(rebuild, self.example3)

    def testFormula(self):
        """
        Perform lexical analysis of a formula, then rebuild it and
        compare that the strings are the same.
        """
        lex = Lexer(self.example5)
        toks = lex.Lex()
        print(toks)
        self.assertEqual(len(toks), 29)
        tmp = [i.literal for i in toks]
        rebuild = "".join([i.literal for i in toks])
        self.assertEqual(rebuild, self.example5)

    def testAcceptLit(self):
        """
        Check the positive case of AcceptLit().
        """
        lex = Lexer(self.example3)
        lex.AcceptLit("cnf")
        lex.AcceptLit("(")
        lex.AcceptLit("test")
        lex.AcceptLit(",")
        lex.AcceptLit("axiom")
        lex.AcceptLit(",")
        lex.AcceptLit("p")
        lex.AcceptLit("(")
        lex.AcceptLit("a")
        lex.AcceptLit(")")
        lex.AcceptLit("|")
        lex.AcceptLit("p")
        lex.AcceptLit("(")
        lex.AcceptLit("f")
        lex.AcceptLit("(")
        # That should be enoug ;-)

    def testErrors(self):
        """
        Provoke different errors.
        """
        lex = Lexer(self.example4)
        self.assertRaises(IllegalCharacterError, lex.Look)

        lex = Lexer(self.example1)
        self.assertRaises(UnexpectedTokenError, lex.CheckTok, Token.EqualSign)

        lex = Lexer(self.example1)
        self.assertRaises(UnexpectedIdentError, lex.CheckLit, "abc")
