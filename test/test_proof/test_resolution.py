#!/usr/bin/env python3
# ----------------------------------
#
# Module resolution.py

"""
This module implements the rules of the simple resolution calculus,
namely binary resolution and factoring.
inference rule:

Binary resolution:

c1|a1     c2|~a2
---------------- where sigma=mgu(a1,a2)
 sigma(c1|c2)

Note that c1 and c2 are arbitrary disjunctions of literals (each of
which may be positive or negative). Both c1 and c2 may be empty.  Both
a1 and a2 are atoms (so a1 and ~a2 are a positive and a negative
literal, respectively).  Also, since | is AC (or, alternatively, the
clauses are unordered multisets), the order of literals is irrelevant.

Clauses are interpreted as implicitly universally quantified
disjunctions of literals. This implies that the scope of the variables
is a single clause. In other words, from a theoretical point of view,
variables in different clauses are different. In practice, we have to
enforce this explicitly by making sure that all clauses used as
premises in an inference are indeed variable disjoint.


Factoring:

   c|a|b
----------  where sigma = mgu(a,b)
sigma(c|a)

Again, c is an arbitray disjunction.


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

from prover.parser.lexer import Lexer
from prover.proof.resolution import *


class TestResolution(unittest.TestCase):
    """
    Unit test class for clauses. Test clause and literal
    functionality.
    """

    def setUp(self):
        """
        Setup function for resolution testing
        """
        print()
        self.spec = """
cnf(c1,axiom,p(a, X)|p(X,a)).
cnf(c2,axiom,~p(a,b)|p(f(Y),a)).
cnf(c3,axiom,p(Z,X)|~p(f(Z),X0)).
cnf(c4,axiom,p(X,X)|p(a,f(Y))).
cnf(c5,axiom,p(X)|~q|p(a)|~q|p(Y)).
cnf(not_p,axiom,~p(a)).
cnf(taut,axiom,p(X4)|~p(X4)).
"""
        lex = Lexer(self.spec)
        self.c1 = clauses.parseClause(lex)
        self.c2 = clauses.parseClause(lex)
        self.c3 = clauses.parseClause(lex)
        self.c4 = clauses.parseClause(lex)
        self.c5 = clauses.parseClause(lex)
        self.c6 = clauses.parseClause(lex)
        self.c7 = clauses.parseClause(lex)

    def testResolution(self):
        """
        Test resolution
        """
        print("Resolution:")
        res1 = resolution(self.c1, 0, self.c2, 0)
        self.assertTrue(res1)
        print(res1)

        res2 = resolution(self.c1, 0, self.c3, 0)
        self.assertTrue(res2 is None)
        print(res2)

        res3 = resolution(self.c2, 0, self.c3, 0)
        self.assertTrue(res3)
        print(res3)

        res4 = resolution(self.c1, 0, self.c3, 1)
        self.assertTrue(res4 is None)
        print(res4)

        res5 = resolution(self.c6, 0, self.c7, 0)
        self.assertTrue(res5)
        print(res5)

    def testFactoring(self):
        """
        Test the factoring inference.
        """
        f1 = factor(self.c1, 0, 1)
        self.assertTrue(f1)
        self.assertTrue(len(f1) == 1)
        print("Factor:", f1)

        f2 = factor(self.c2, 0, 1)
        self.assertTrue(f2 is None)
        print(f2)

        f4 = factor(self.c4, 0, 1)
        self.assertTrue(f4 is None)
        print(f4)

        f5 = factor(self.c5, 1, 3)
        self.assertTrue(f5)
        print(f5)

