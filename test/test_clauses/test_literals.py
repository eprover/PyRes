#!/usr/bin/env python3
# ----------------------------------
#
# Module literal.py

"""
A simple implementation of first-order atoms and literals.

We assume a set of function symbols F (with associated arities) and
variables symbols as defined in terms.py. We now also assume a set P
of predicate symbols, and extend the arity function to
ar:F \cup P ->N

The set of all first-order atoms over P, F, V, Atom(P,F,V) is defined
as follows:
- If t1, ... t_n are in Term(F,V) and p|n is in P, then p(t1,..., tn)
  is in Atom(P,F,V)
- Atom(P,F,V) is the smallest set with this property.


Assume F={f|2, g|1, a|0, b|0}, V={X, Y, ...} and P={p|1, q|2}. Then
the following are atoms:

p(a)
q(X, g(g(a)))
p(f(b, Y))

Because of the special role of equality for theorem proving, we
usually assume "="|2 and "!="|2 are in P. In the concrete syntax,
these symbols are written as infix symbols, i.e. we write a=b, not
"=(a, b)".

A literal is a signed atom. A positive literal is syntactically
identical to its atom. A negative literal consists of the negation
sign, ~, followed by an atom.

Thus, we can describe the set
Literals(P,F,V) = {~a | a in Atom(P,F,V)} \cup Atom(P,F,V)

We establish the convention that t1!=t2 is equivalent to ~t1=t2 and
~t1!=t2 is equivalent to t1=t2, and only use the respective later
forms internally. In other words, the symbol != only occurs during
parsing and printing.


Copyright 2010-2020 Stephan Schulz, schulz@eprover.org

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

from prover.clauses.literals import *
from prover.proof.substitutions import BTSubst


class TestLiterals(unittest.TestCase):
    """
    Unit test class for literals.
    """

    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.input1 = "p(X)  ~q(f(X,a), b)  ~a=b  a!=b  ~a!=f(X,b) p(X) ~p(X) p(a)"
        self.input2 = "p(X)|~q(f(X,a), b)|~a=b|a!=b|~a!=f(X,b)"
        self.input3 = "$false"
        self.input4 = "$false|~q(f(X,a), b)|$false"
        self.input5 = "p(a)|p(f(X))"

        lexer = Lexer(self.input1)
        self.a1 = parseLiteral(lexer)
        self.a2 = parseLiteral(lexer)
        self.a3 = parseLiteral(lexer)
        self.a4 = parseLiteral(lexer)
        self.a5 = parseLiteral(lexer)
        self.a6 = parseLiteral(lexer)
        self.a7 = parseLiteral(lexer)
        self.a8 = parseLiteral(lexer)

    def testLiterals(self):
        """
        Test that basic literal literal functions work
        correctly.
        """

        vars = set()
        print(self.a1)
        self.assertTrue(self.a1.isPositive())
        self.assertTrue(not self.a1.isEquational())
        self.a1.collectVars(vars)
        self.assertEqual(len(vars), 1)
        self.assertEqual(self.a1.collectFuns(), {"p"})
        self.assertTrue(self.a1.isInferenceLit())
        self.a1.setInferenceLit(False)
        self.assertTrue(not self.a1.isInferenceLit())

        print(self.a2)
        self.assertTrue(self.a2.isNegative())
        self.assertTrue(not self.a2.isEquational())
        self.a2.collectVars(vars)
        self.assertEqual(len(vars), 1)
        self.assertEqual(self.a2.collectFuns(), {"q", "f", "a", "b"})

        print(self.a3)
        self.assertTrue(self.a3.isNegative())
        self.assertTrue(self.a3.isEquational())
        self.assertTrue(self.a3.isEqual(self.a4))
        self.a3.collectVars(vars)
        self.assertEqual(len(vars), 1)

        print(self.a4)
        self.assertTrue(self.a4.isNegative())
        self.assertTrue(self.a4.isEquational())
        self.assertTrue(self.a4.isEqual(self.a3))
        self.a4.collectVars(vars)
        self.assertEqual(len(vars), 1)

        print(self.a5)
        self.assertTrue(not self.a5.isNegative())
        self.assertTrue(self.a5.isEquational())
        self.a5.collectVars(vars)
        self.assertEqual(len(vars), 1)

        print(self.a6, self.a7)
        self.assertTrue(self.a6.isOpposite(self.a7))
        self.assertTrue(self.a7.isOpposite(self.a6))
        self.assertTrue(not self.a6.isOpposite(self.a6))
        self.assertTrue(not self.a6.isOpposite(self.a1))

        self.assertEqual(self.a1.predicateAbstraction(), (True, "p"))
        self.assertEqual(self.a2.predicateAbstraction(), (False, "q"))
        self.assertEqual(self.a3.predicateAbstraction(), (False, "="))

    def testPropProps(self):
        """
        Test if literals are correctly handled as propositional
        constants.
        """
        lex = Lexer("$true $false ~$false ~$true p(a)")
        l1 = parseLiteral(lex)
        l2 = parseLiteral(lex)
        l3 = parseLiteral(lex)
        l4 = parseLiteral(lex)
        l5 = parseLiteral(lex)

        self.assertTrue(l1.isPropTrue())
        self.assertTrue(not l1.isPropFalse())

        self.assertTrue(not l2.isPropTrue())
        self.assertTrue(l2.isPropFalse())

        self.assertTrue(l3.isPropTrue())
        self.assertTrue(not l3.isPropFalse())

        self.assertTrue(not l4.isPropTrue())
        self.assertTrue(l4.isPropFalse())

        self.assertTrue(not l5.isPropTrue())
        self.assertTrue(not l5.isPropFalse())

        l6 = l1.negate()
        self.assertTrue(not l6.isPropTrue())
        self.assertTrue(l6.isPropFalse())

        l7 = l2.negate()
        self.assertTrue(l7.isPropTrue())
        self.assertTrue(not l7.isPropFalse())

    def testAtoms(self):
        """
        Test atom parsing and printing.
        """
        lex = Lexer("p(a) a=b a!=b")
        a = parseAtom(lex)
        print(atom2String(a))
        a = parseAtom(lex)
        print(atom2String(a))
        a = parseAtom(lex)
        print(atom2String(a))

    def testLitWeight(self):
        """
        Test the weight function.
        """
        self.assertEqual(self.a1.weight(2, 1), 3)
        self.assertEqual(self.a2.weight(2, 1), 9)
        self.assertEqual(self.a3.weight(2, 1), 6)
        self.assertEqual(self.a4.weight(2, 1), 6)
        self.assertEqual(self.a5.weight(2, 1), 9)

    def testMatch(self):
        """
        Test literal matching.
        """
        self.assertTrue(self.a1.match(self.a1, BTSubst()))
        self.assertTrue(not self.a1.match(self.a2, BTSubst()))

        self.assertTrue(self.a1.match(self.a8, BTSubst()))
        self.assertTrue(not self.a8.match(self.a1, BTSubst()))

        self.assertTrue(not self.a1.match(self.a2, BTSubst()))
        self.assertTrue(not self.a2.match(self.a1, BTSubst()))

    def testLitList(self):
        """
        Test literal list parsing and printing.
        """
        lexer = Lexer(self.input2)
        l2 = parseLiteralList(lexer)
        print(literalList2String(l2))
        self.assertEqual(len(l2), 5)

        lexer = Lexer(self.input3)
        l3 = parseLiteralList(lexer)
        print(literalList2String(l3))
        self.assertEqual(len(l3), 0)

        lexer = Lexer(self.input4)
        l4 = parseLiteralList(lexer)
        print(literalList2String(l4))
        self.assertEqual(len(l4), 1)

        lexer = Lexer(self.input5)
        l5 = parseLiteralList(lexer)
        print(literalList2String(l5))
        self.assertEqual(len(l5), 2)

        self.assertTrue(litInLitList(l4[0], l4))
        self.assertTrue(not litInLitList(self.a6, l4))

        self.assertTrue(oppositeInLitList(self.a7, l2))
        self.assertTrue(not oppositeInLitList(self.a7, l4))

    def testSig(self):
        """
        Test signature collection.
        """
        sig = self.a1.collectSig()
        self.a2.collectSig(sig)
        self.a3.collectSig(sig)
        self.a4.collectSig(sig)
        self.a5.collectSig(sig)
        self.a6.collectSig(sig)
        self.a7.collectSig(sig)
        self.a8.collectSig(sig)
        sig.addFun("mult", 2)

        print(sig)
        self.assertTrue(sig.isPred("q"))
        self.assertTrue(not sig.isPred("unknown"))
        self.assertTrue(not sig.isPred("a"))
        self.assertTrue(sig.isFun("a"))
        self.assertTrue(not sig.isFun("unknown"))
        self.assertTrue(not sig.isFun("q"))

        self.assertEqual(sig.getArity("b"), 0)
        self.assertEqual(sig.getArity("p"), 1)


if __name__ == '__main__':
    unittest.main()
