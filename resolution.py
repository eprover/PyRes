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
from lexer import Lexer
import substitutions
from unification import mgu
from literals import Literal
from derivations import flatDerivation
import clauses


def resolution(clause1, lit1, clause2, lit2):
    """
    Implementation of the Resolution rule. lit1 and lit2 are indices
    of literals in clause1 and clause2, respectively, so clause1|lit1
    and clause2|lit2 are literals.

    Try to resolve clause1|lit1 against clause2|lit2. If this is
    possible, return the resolvent. Otherwise, return None.
    """
    l1 = clause1.getLiteral(lit1)
    l2 = clause2.getLiteral(lit2)
    if l1.isNegative() == l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    if sigma == None:
        return None
    lits1 = [l.instantiate(sigma) for l in clause1.literals if l!=l1]
    lits2 = [l.instantiate(sigma) for l in clause2.literals if l!=l2]
    lits1.extend(lits2)
    res = clauses.Clause(lits1)
    res.removeDupLits()
    res.setDerivation(flatDerivation("resolution", [clause1, clause2]))
    return res


def factor(clause, lit1, lit2):
    """
    Check if it is possible to form a factor between lit1 and lit2. If
    yes, return it, otherwise return None.
    """
    l1 = clause.getLiteral(lit1)
    l2 = clause.getLiteral(lit2)
    if l1.isNegative() != l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    if sigma == None:
        return None
    lits = [l.instantiate(sigma) for l in clause.literals if l!=l2]
    res = clauses.Clause(lits)
    res.removeDupLits()
    res.setDerivation(flatDerivation("factor", [clause]))
    return res




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
        res1 = resolution(self.c1, 0, self.c2,0)
        self.assertTrue(res1)
        print(res1)

        res2 = resolution(self.c1, 0, self.c3,0)
        self.assertTrue(res2==None)
        print(res2)

        res3 = resolution(self.c2, 0, self.c3,0)
        self.assertTrue(res3)
        print(res3)

        res4 = resolution(self.c1, 0, self.c3,1)
        self.assertTrue(res4==None)
        print(res4)

        res5 = resolution(self.c6, 0, self.c7,0)
        self.assertTrue(res5)
        print(res5)

    def testFactoring(self):
        """
        Test the factoring inference.
        """
        f1 = factor(self.c1,0,1)
        self.assertTrue(f1)
        self.assertTrue(len(f1)==1)
        print("Factor:", f1)

        f2 = factor(self.c2,0,1)
        self.assertTrue(f2==None)
        print(f2)

        f4 = factor(self.c4,0,1)
        self.assertTrue(f4==None)
        print(f4)

        f5 = factor(self.c5,1,3)
        self.assertTrue(f5)
        print(f5)

if __name__ == '__main__':
    unittest.main()
