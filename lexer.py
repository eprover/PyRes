#!/usr/bin/env python2.7
# ----------------------------------
#
# Module lexer.py

"""
A simple lexical analyser that converts a string into a sequence of
tokens. 

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
import string
import re


class ScannerError(Exception):
    """
    A class representing all errors that the scanner can produce.
    """
    def __init__(self):
        self.name = "ScannerError"
        self.value = "<none>"        
    
    def __repr__(self):
        return name+"("+repr(self.value)+")"


class UnexpectedTokenError(ScannerError):
    """
    Class representing an unexpected token error.
    """
    def __init__(self, token):
        self.value = token


class IllegalCharacterError(ScannerError):
    """
    Class representing an unexpexted character error
    """
    def __init__(self, char):
        self.value = char
    


nl_re  = re.compile("\n")


class Ident:
    """
    Dummy class for generating distinct named objects.
    """

    def __init__(self, name = ""):
        self.name = name

    def __repr__(self):
        return self.name
    

class Token:
    """
    Represent a single token with name, position, and print
    representation.
    """
    NoToken        = Ident("No Token")
    WhiteSpace     = Ident("White Space")
    Comment        = Ident("Comment")
    IdentUpper     = Ident("Identifier starting with capital letter")
    IdentLower     = Ident("Identifier starting with lower case letter")
    Integer        = Ident("Positive or negative Integer")         
    FullStop       = Ident(". (full stop)")
    OpenPar        = Ident("(")
    ClosePar       = Ident(")")
    Comma          = Ident(",")
    EqualSign      = Ident("=")
    Negation       = Ident("~")
    Or             = Ident("|")
    And            = Ident("&")
    Implies        = Ident("->")
    Equiv          = Ident("<=>")
    EOFToken       = Ident("*EOF*")
   
    def __init__(self, type, literal, source, pos):
        self.type    = type;
        self.literal = literal;
        self.source  = source;
        self.pos     = pos

    def __repr__(self):
        return repr( (self.type, self.literal) )

    def linepos(self):
        """
        Return the line number of the token by counting all the
        newlines in the position up to the current token.
        """
        return len(nl_re.findall(self.source[:self.pos]))+1
    

class Lexer:
    """
    Lexical analysier. This will convert a string into a sequence of
    tokens that can be inspected and processed in-order. It is a bit
    of an overkill for the simple application, but makes actual
    parsing later much easier and more robust than a quicker hack.
    """

    # This list is traversed in order, the first match is
    # returned. This makes it much easier than "longest match", and
    # I have not yet seen a grammar where this causes trouble.
    token_defs = [        
        (re.compile("\."),                    Token.FullStop),
        (re.compile("\("),                    Token.OpenPar),
        (re.compile("\)"),                    Token.ClosePar),
        (re.compile(","),                     Token.Comma),
        (re.compile("="),                     Token.EqualSign),
        (re.compile("~"),                     Token.Negation),
        (re.compile("\|"),                    Token.Or),
        (re.compile("&"),                     Token.And),
        (re.compile("->"),                    Token.Implies),
        (re.compile("<=>"),                   Token.Equiv),
	(re.compile("\s+"),                   Token.WhiteSpace),
        (re.compile("[a-z][_a-z0-9_A-Z]*"),   Token.IdentLower),
        (re.compile("[_A-Z][_a-z0-9_A-Z]*"),  Token.IdentUpper),
        (re.compile("#[^\n]*"),               Token.Comment)
        ]
    
    def __init__(self, source, name="user string"):
        """
        Initialize the lexer with the string (=sequence of bytes) to
        be split into tokens. The second argument can be used to
        denote the source of the data, e.g. a filename.
        """
        self.token_stack = []
        self.source = source
        self.pos = 0
        self.name = name

    def Push(self, token):
        """
        Return a token to the token stack. This allows basically
        unlimited look-ahead under user control.
        """
        self.token_stack.append(token)

    def Look(self):
        """
        Return the next token without consuming it.
        """
        res = self.Next()
        self.Push(res)
        return res

    def TestTok(self, tokens):
        """
        Take a list of expected token types. Return True if the
        next token is expected, False otherwise.
        """
        try:
            # If tokens is a list, we accept all elements from the
            # list.
            return self.Look().type in tokens
        except TypeError:
            # Otherwise, it is a single token whose type has to be
            # matched.
            return self.Look().type == tokens

    def CheckTok(self, tokens):
        """
        Take a list of expected token types. If the next token is
        not among the expected ones, exit with an error. Otherwise do
        nothing. 
        """
        if not self.TestTok(tokens):
            raise UnexpectedTokenError(
                repr(self.Look().literal)+
                " not "+repr(tokens))

    def AcceptTok(self, tokens):
        """
        Take a list of expected token types. If the next token is
        among the expected ones, consume and return it.
        Otherwise, exit with an error.
        """
        self.CheckTok(tokens)
        return self.Next()
    
    def Next(self):
        """
        Return next semantically relevant token.
        """
        res = self.NextUnfiltered();
        while res.type in [Token.WhiteSpace, Token.Comment]:
            res = self.NextUnfiltered();
        return res;

    def NextUnfiltered(self):
        """
        Return next token, including tokens ignored by most
        languages. 
        """
        if len(self.token_stack) > 0:
            return self.token_stack.pop()
        else:
            old_pos = self.pos
            if self.source[old_pos:] == "":
                return Token(Token.EOFToken, "", self.source, old_pos)
            for i in self.token_defs:
                # Go through all the token definitions and process the
                # first one that matchs.
                mr = i[0].match(self.source, self.pos)
                if mr:
                    literal = self.source[mr.start():mr.end()]
                    self.pos = mr.end()
                    type = i[1]
                    break
            if not mr:
                raise IllegalCharacterError(self.source[self.pos:self.pos+4]+"...")

            return Token(type, literal, self.source, old_pos)

    def Lex(self):
        """
        Return a list of all tokens in the source.
        """
        res = []
        while not self.TestTok(Token.EOFToken):
            res.append(self.Next())
        return res


class TestLexer(unittest.TestCase):
    """
    Test the lexer functions.
    """
    def setUp(self):
        self.example1 = "f(X,g(a,b))"
        self.example2 = "# Comment\nf(X,g(a,b))"
        self.example3 = "cnf(test,axiom,p(a)|p(f(X)))."
        
    def testLex(self):
        """
        Test that comments and whitespace are normally ignored.
        """
        lex1=Lexer(self.example1)
        lex2=Lexer(self.example2)
        res1 = [(i.type, i.literal) for i in lex1.Lex()] 
        res2 = [(i.type, i.literal) for i in lex2.Lex()]
        self.assertEqual(res1, res2)

    def testTerm(self):
        """
        Test that self.example 1 is split into the expected tokens.
        """
        lex1=Lexer(self.example1)
        lex1.AcceptTok([Token.IdentLower]) # f
        lex1.AcceptTok([Token.OpenPar])    # (
        lex1.AcceptTok([Token.IdentUpper]) # X
        lex1.AcceptTok([Token.Comma])      # ,
        lex1.AcceptTok([Token.IdentLower]) # g
        lex1.AcceptTok([Token.OpenPar])    # (
        lex1.AcceptTok([Token.IdentLower]) # a
        lex1.AcceptTok([Token.Comma])      # ,
        lex1.AcceptTok([Token.IdentLower]) # b
        lex1.AcceptTok([Token.ClosePar])   # )
        lex1.AcceptTok([Token.ClosePar])   # )

    def testClause(self):
        """
        Perform lexical analysis of a clause, then rebuild it and
        compare that the strings are the same.
        """
        lex = Lexer(self.example3)
        toks = lex.Lex()
        print toks
        self.assertEqual(len(toks), 20)
        tmp = [i.literal for i in toks]
        rebuild = "".join([i.literal for i in toks])
        self.assertEqual(rebuild, self.example3)
        

if __name__ == '__main__':
    unittest.main()
