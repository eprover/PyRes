"""
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

from prover.optimizations.heuristics import *
from prover.parser.lexer import Lexer
from prover.clauses.clauses import parseClause


class TestHeuristics(unittest.TestCase):
    """
    Test heuristic evaluation functions.
    """

    def setUp(self):
        """
        Setup function for tests. Create some clauses to test
        evaluations on.
        """

        print()
        self.spec = """
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
        self.c1 = parseClause(lexer)
        self.c2 = parseClause(lexer)
        self.c3 = parseClause(lexer)
        self.c4 = parseClause(lexer)
        self.c5 = parseClause(lexer)
        self.c6 = parseClause(lexer)
        self.c7 = parseClause(lexer)
        self.c8 = parseClause(lexer)

    def testFIFO(self):
        """
        Test that FIFO evaluation works as expected.
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
        self.assertTrue(e1 < e2)
        self.assertTrue(e2 < e3)
        self.assertTrue(e3 < e4)
        self.assertTrue(e4 < e5)
        self.assertTrue(e5 < e6)
        self.assertTrue(e6 < e7)
        self.assertTrue(e7 < e8)

    def testSymbolCount(self):
        """
        Test that symbol counting works as expected.
        """
        eval = SymbolCountEvaluation(2, 1)
        e1 = eval(self.c1)
        e2 = eval(self.c2)
        e3 = eval(self.c3)
        e4 = eval(self.c4)
        e5 = eval(self.c5)
        e6 = eval(self.c6)
        e7 = eval(self.c7)
        e8 = eval(self.c8)
        self.assertEqual(e1, self.c1.weight(2, 1))
        self.assertEqual(e2, self.c2.weight(2, 1))
        self.assertEqual(e3, self.c3.weight(2, 1))
        self.assertEqual(e4, self.c4.weight(2, 1))
        self.assertEqual(e5, self.c5.weight(2, 1))
        self.assertEqual(e6, self.c6.weight(2, 1))
        self.assertEqual(e7, self.c7.weight(2, 1))
        self.assertEqual(e8, self.c8.weight(2, 1))

    def testEvalStructure(self):
        """
        Test composite evaluations.
        """
        eval_funs = EvalStructure([(SymbolCountEvaluation(2, 1), 2),
                                   (FIFOEvaluation(), 1)])

        evals = eval_funs.evaluate(self.c1)
        self.assertEqual(len(evals), 2)
        self.assertEqual(eval_funs.nextEval(), 0)
        self.assertEqual(eval_funs.nextEval(), 0)
        self.assertEqual(eval_funs.nextEval(), 1)
        self.assertEqual(eval_funs.nextEval(), 0)
        self.assertEqual(eval_funs.nextEval(), 0)
        self.assertEqual(eval_funs.nextEval(), 1)
