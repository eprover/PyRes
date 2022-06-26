#!/usr/bin/env python3
# ----------------------------------
#
# Module formulacnf.py

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

from prover.clauses.derivations import enableDerivationOutput, toggleDerivationOutput
from prover.clauses.formulacnf import *
from prover.clauses.formulas import parseFormula, termIsCompound, termArgs, parseWFormula
from prover.parser.lexer import Lexer, Token


class TestCNF(unittest.TestCase):
    """
    Test cases for clausification.
    """

    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.formulas = """
        ![X]:(a(X) ~| ~a=b)
        ![X]:(a(X)|b(X)|?[X,Y]:(p(X,f(Y))<~>q(g(a),X)))
        ![X]:(a(X) <= ~a=b)
        ((((![X]:a(X))|b(X))|(?[X]:(?[Y]:p(X,f(Y)))))~&q(g(a),X))
        ![X]:(a(X)|$true)
        """
        lex = Lexer(self.formulas)
        self.f1 = parseFormula(lex)
        self.f2 = parseFormula(lex)
        self.f3 = parseFormula(lex)
        self.f4 = parseFormula(lex)
        self.f5 = parseFormula(lex)
        self.simple_ops = {"", "!", "?", "~", "&", "|", "=>", "<=>"}
        self.nnf_ops = {"", "!", "?", "&", "|"}

        self.covformulas = """
        (a|$true)
        ($true|a)
        (a|$false)
        ($false|a)
        (a|a)
        (a&$true)
        ($true&a)
        (a&$false)
        ($false&a)
        (a&a)
        (a=>$true)
        ($true=>a)
        (a=>$false)
        ($false=>a)
        (a=>a)
        (a<=>$true)
        ($true<=>a)
        (a<=>$false)
        ($false<=>a)
        (a<=>a)
        ![X]:(a<=>a)
        ?[X]:(a<=>a)
        a<=>b
        """

        self.testformulas = """
 fof(t12_autgroup,conjecture,(
    ! [A] :
      ( ( ~ v3_struct_0(A)
        & v1_group_1(A)
        & v3_group_1(A)
        & v4_group_1(A)
        & l1_group_1(A) )
     => r1_tarski(k4_autgroup(A),k1_fraenkel(u1_struct_0(A),u1_struct_0(A))) ) )).

fof(abstractness_v1_group_1,axiom,(
    ! [A] :
      ( l1_group_1(A)
     => ( v1_group_1(A)
       => A = g1_group_1(u1_struct_0(A),u1_group_1(A)) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).
fof(cc1_fraenkel,axiom,(
    ! [A] :
      ( v1_fraenkel(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ( v1_relat_1(B)
            & v1_funct_1(B) ) ) ) )).

fof(cc1_funct_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) )).

fof(cc1_funct_2,axiom,(
    ! [A,B,C] :
      ( m1_relset_1(C,A,B)
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A,B) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) )).
fof(testscosko, axiom, (![X]:?[Y]:((p(X)&q(X))|q(X,Y))|a)).
        """

    def testOpSimplification(self):
        """
        Test that operator simplification works.
        """
        f, m = formulaOpSimplify(self.f1)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f, m = formulaOpSimplify(self.f2)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f, m = formulaOpSimplify(self.f3)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f, m = formulaOpSimplify(self.f4)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f, m = formulaOpSimplify(self.f5)
        self.assertTrue(not m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

    def checkSimplificationResult(self, f):
        """
        Simplification results in a formula that does not contain
        the constant predicates $true or $false. The only exception is
        when the whole formula has been has been reduced to a single
        literal (in which case it can be either $true, or $false, or
        any other literal).
        """

        funs = f.collectFuns()
        if f.isPropConst(True) or f.isPropConst(False):
            self.assertTrue(funs in [{"$true"}, {"$false"}])
        else:
            self.assertTrue("$true" not in funs)
            self.assertTrue("$false" not in funs)

    def testSimplification(self):
        """
        Test that simplification works.
        """
        f, m = formulaOpSimplify(self.f1)
        f, m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f, m = formulaOpSimplify(self.f2)
        f, m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f, m = formulaOpSimplify(self.f3)
        f, m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f, m = formulaOpSimplify(self.f4)
        f, m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f, m = formulaOpSimplify(self.f5)
        f, m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        lex = Lexer(self.covformulas)
        while not lex.TestTok(Token.EOFToken):
            f = parseFormula(lex)
            f, m = formulaOpSimplify(f)
            f, m = formulaSimplify(f)
            self.checkSimplificationResult(f)

    def checkNNFResult(self, f):
        """
        A simplified formula is either $true/$false, or it only
        contains &, |, !, ? as operators (~ is shifted into the
        literals).
        """

        print("NNF:", f)
        if f.isPropConst(True) or f.isPropConst(False):
            funs = f.collectFuns()
            self.assertTrue(funs in [{"$true"}, {"$false"}])
        else:
            ops = f.collectOps()
            self.assertTrue(ops <= self.nnf_ops)

    def testNNF(self):
        """
        Test NNF transformation
        """
        f, m = formulaOpSimplify(self.f1)
        f, m = formulaSimplify(f)
        f, m = formulaNNF(f, 1)
        self.checkNNFResult(f)

        f, m = formulaOpSimplify(self.f2)
        f, m = formulaSimplify(f)
        f, m = formulaNNF(f, 1)
        self.checkNNFResult(f)

        f, m = formulaOpSimplify(self.f3)
        f, m = formulaSimplify(f)
        f, m = formulaNNF(f, 1)
        self.checkNNFResult(f)

        f, m = formulaOpSimplify(self.f4)
        f, m = formulaSimplify(f)
        f, m = formulaNNF(f, 1)
        self.checkNNFResult(f)

        f, m = formulaOpSimplify(self.f5)
        f, m = formulaSimplify(f)
        f, m = formulaNNF(f, 1)
        self.checkNNFResult(f)

        lex = Lexer(self.covformulas)
        while not lex.TestTok(Token.EOFToken):
            f = parseFormula(lex)
            f, m = formulaOpSimplify(f)
            f, m = formulaSimplify(f)
            f, m = formulaNNF(f, 1)
            self.checkNNFResult(f)

    def testMiniScope(self):
        """
        Test Miniscoping.
        """
        lex = Lexer("""
        ![X]:(p(X)|q(a))
        ?[X]:(p(a)&q(X))
        ![X]:(p(X)&q(X))
        ?[X]:(p(X)|q(X))
        ![X]:(p(X)|q(X))
        ![X,Y]:?[Z]:(p(Z)|q(X))
        """)
        res = [True, True, True, True, False, True]

        while not lex.TestTok(Token.EOFToken):
            expected = res.pop(0)
            f = parseFormula(lex)
            f1, m = formulaMiniScope(f)
            print(f, f1, m, expected)
            self.assertEqual(expected, m)
            if m:
                self.assertTrue(not f1.isQuantified())

    def testRenaming(self):
        """
        Test variable renaming
        """
        lex = Lexer("![X]:(p(X)|![X]:(q(X)&?[X]:r(X)))")
        f = parseFormula(lex)

        v1 = f.collectVars()
        self.assertEqual(v1, set(["X"]))
        v2 = f.collectFreeVars()
        self.assertEqual(v2, set())

        f1 = formulaVarRename(f)
        print(f, f1)

        v1 = f1.collectVars()
        self.assertEqual(len(v1), 3)
        v2 = f1.collectFreeVars()
        self.assertEqual(v2, set())

    def testSkolemSymbols(self):
        """
        Check if Skolem symbol construction works.
        """
        symbols = []
        for i in range(10):
            newsymbol = skolemGenerator.newSkolemSymbol()
            self.assertTrue(newsymbol not in symbols)
            symbols.append(newsymbol)

        var = ["X", "Y"]
        for i in range(10):
            t = skolemGenerator(var)
            self.assertTrue(termIsCompound(t))
            self.assertEqual(termArgs(t), var)

    def preprocFormula(self, f):
        """
        Bring formula into miniscoped variable normalized NNF.
        """
        f, m = formulaOpSimplify(f)
        f, m = formulaSimplify(f)
        f, m = formulaNNF(f, 1)
        f, m = formulaMiniScope(f)
        f = formulaVarRename(f)
        return f

    def testSkolemization(self):
        """
        Test skolemization.
        """
        f = self.preprocFormula(self.f2)
        f = formulaSkolemize(f)
        self.assertTrue("?" not in f.collectOps())
        print(f)

        f = self.preprocFormula(self.f3)
        f = formulaSkolemize(f)
        self.assertTrue("?" not in f.collectOps())
        print(f)

        f = self.preprocFormula(self.f4)
        f = formulaSkolemize(f)
        self.assertTrue("?" not in f.collectOps())
        print(f)

    def testShiftQuantors(self):
        """
        Test shifting of quantors out.
        """
        f = self.preprocFormula(self.f2)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        if "!" in f.collectOps():
            self.assertEqual(f.op, "!")

        f = self.preprocFormula(self.f3)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        if "!" in f.collectOps():
            self.assertEqual(f.op, "!")

        f = self.preprocFormula(self.f4)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        if "!" in f.collectOps():
            self.assertEqual(f.op, "!")

    def testDistributeDisjunctions(self):
        """
        Test ConjunctiveNF.
        """
        f = self.preprocFormula(self.f2)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        f = formulaDistributeDisjunctions(f)
        print(f)
        self.assertTrue(f.isCNF())

        f = self.preprocFormula(self.f3)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        f = formulaDistributeDisjunctions(f)
        print(f)
        self.assertTrue(f.isCNF())

        f = self.preprocFormula(self.f4)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        f = formulaDistributeDisjunctions(f)
        print(f)
        self.assertTrue(f.isCNF())

    def testCNFization(self):
        """
        Test conversion of wrapped formulas into conjunctive normal
        form.
        """
        lex = Lexer(self.testformulas)

        while not lex.TestTok(Token.EOFToken):
            wf = parseWFormula(lex)
            wf = wFormulaCNF(wf)
            enableDerivationOutput()
            self.assertTrue(wf.formula.isCNF())
            deriv = wf.orderedDerivation()
            print("==================")
            for s in deriv:
                print(s)
            toggleDerivationOutput()

    def testClausification(self):
        """
        Test conversion of wrapped formulas into lists of clauses.
        """
        lex = Lexer(self.testformulas)

        while not lex.TestTok(Token.EOFToken):
            wf = parseWFormula(lex)
            clauses = wFormulaClausify(wf)
            enableDerivationOutput()
            print("==================")
            for c in clauses:
                print(c)
            toggleDerivationOutput()
