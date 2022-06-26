#!/usr/bin/env python3
# ----------------------------------
#
# Module formulas.py

"""
Copyright 2011-2019 Stephan Schulz, schulz@eprover.org

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

from prover.clauses.derivations import toggleDerivationOutput
from prover.clauses.formulas import *
from prover.clauses.terms import *


class TestFormulas(unittest.TestCase):
    """
    Unit test class for clauses. Test clause and literal
    functionality.
    """

    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.nformulas = """
        ![X]:(p(X) | ~a=b)
        (![X]:a(X)|b(X)|?[X,Y]:(p(X,f(Y))))<=>q(g(a),X)
        ((((![X]:a(X))|b(X))|(?[X]:(?[Y]:p(X,f(Y)))))<=>q(g(a),X))
        ![X]:(p(X) | ~q(X))

"""
        self.wformulas = """
        fof(small, axiom, ![X]:(p(X) | ~a=b)).
        fof(complex, conjecture, (![X]:r(X)|p(X)|?[X,Y]:(p(X,f(Y))))<=>q(g(a),X)).
        fof(clean, conjecture,
                   ((((![X]:p(X))|r(X))|(?[X]:(?[Y]:p(X,f(Y)))))<=>q(g(a),X))).
        fof(weird, weird, ![X]:(p(X) | ~q(X))).

"""

    def testNakedFormula(self):
        """
        Test that basic parsing and functionality works.
        """
        lex = Lexer(self.nformulas)
        f1 = parseFormula(lex)
        print("f1:", f1)
        f2 = parseFormula(lex)
        print("f2:", f2)
        f3 = parseFormula(lex)
        print("f3:", f3)
        f4 = parseFormula(lex)
        print("f4:", f4)
        self.assertTrue(f2.isEqual(f3))
        self.assertTrue(f3.isEqual(f2))
        self.assertTrue(not f1.isEqual(f2))
        self.assertTrue(not f2.isEqual(f1))
        self.assertTrue(not f1.isEqual(f4))

        self.assertEqual(f1.collectFreeVars(), set())
        self.assertEqual(f2.collectFreeVars(), {"X"})
        self.assertEqual(f3.collectFreeVars(), {"X"})

        self.assertEqual(f1.collectVars(), {"X"})
        self.assertEqual(f2.collectVars(), {"X", "Y"})
        self.assertEqual(f3.collectVars(), {"X", "Y"})

        self.assertTrue(f1.isQuantified())
        self.assertTrue(not f2.isQuantified())
        self.assertTrue(not f3.isQuantified())
        self.assertTrue(not f1.hasSubform1())
        self.assertTrue(f2.hasSubform1())
        self.assertTrue(f3.hasSubform1())
        self.assertTrue(f1.hasSubform2())
        self.assertTrue(f2.hasSubform2())
        self.assertTrue(f3.hasSubform2())

    def testPropositional(self):
        """
        Check propositional literal recognition and manipulation.
        """
        lex = Lexer("$true $false $true|$false ")
        t = parseFormula(lex)
        f = parseFormula(lex)
        c = parseFormula(lex)
        self.assertTrue(t.isPropConst(True))
        self.assertTrue(not t.isPropConst(False))
        self.assertTrue(f.isPropConst(False))
        self.assertTrue(not f.isPropConst(True))

        self.assertTrue(not c.isPropConst(True))
        self.assertTrue(not c.isPropConst(False))

    def testCollectOps(self):
        """
        Test if operator and funtion symbol collection works.
        """
        lex = Lexer("a&(b|~c)    "
                    "(a=>b)<=(c<=>?[X]:p(X))"
                    "(a~&(b<~>(c=>d)))~|![Y]:e(Y)")
        f = parseFormula(lex)
        self.assertEqual(f.collectOps(), {"", "&", "|", "~"})
        self.assertEqual(f.collectFuns(), {"a", "b", "c"})

        f = parseFormula(lex)
        self.assertEqual(f.collectOps(), {"", "=>", "<=", "?", "<=>"})
        self.assertEqual(f.collectFuns(), {"a", "b", "c", "p"})

        f = parseFormula(lex)
        self.assertEqual(f.collectOps(),
                         {"", "~&", "~|", "!", "<~>", "=>"})
        self.assertEqual(f.collectFuns(), {"a", "b", "c", "d", "e"})

    def testCNFTest(self):
        """
        Check the CNF test.
        """
        lex = Lexer("""
        a=>b
        a & (a|(b=>c))
        ![X]:((a|b)&c)
        ![X]:![Y]:((a|b)&(?[X]:c(X)))
        ![X]:(a & (a|b|c) & (a|b|c|d))
        """)
        expected = [False, False, True, False, True]
        while not lex.TestTok(Token.EOFToken):
            f = parseFormula(lex)
            res = expected.pop(0)
            self.assertEqual(f.isCNF(), res)

    def testSplitter(self):
        """
        Test splitting of conjunctions/disjunktions.
        """
        lex = Lexer("""
        a=>b
        a & (a|(b=>c))
        ![X]:((a|b)&c)
        ![X]:![Y]:((a|b)&(?[X]:c(X)))
        ![X]:(a & (a|b|c) & (a|b|c|d))
        a|(b&c)|(b<=>d)|![X]:p(X)
        """)
        cexpected = [1, 2, 2, 2, 3, 1]
        dexpected = [1, 1, 1, 1, 1, 4]

        while not lex.TestTok(Token.EOFToken):
            f = parseFormula(lex)
            f = f.getMatrix()

            cs = f.conj2List()
            res = cexpected.pop(0)
            self.assertEqual(len(cs), res)

            ds = f.disj2List()
            res = dexpected.pop(0)
            self.assertEqual(len(ds), res)

    def testWrappedFormula(self):
        """
        Test basic parsing and output of wrapped formulae.
        """
        lex = Lexer(self.wformulas)
        f1 = parseWFormula(lex)
        print(f1)
        f2 = parseWFormula(lex)
        print(f2)
        f3 = parseWFormula(lex)
        print(f3)
        f4 = parseWFormula(lex)
        print(f4)
        toggleDerivationOutput()
        print(f1)
        print(f2)
        print(f3)
        print(f4)
        toggleDerivationOutput()

        sig = f1.collectSig()
        f2.collectSig(sig)
        f3.collectSig(sig)
        f4.collectSig(sig)

        print(sig)
        sig.isPred("q")
        sig.isPred("r")
        sig.isFun("a")
        sig.isConstant("a")


if __name__ == '__main__':
    unittest.main()
