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

from prover.optimizations.indexing import *
from prover.clauses import clauses
from prover.parser.lexer import Lexer
from prover.clauses.terms import termFunc


class TestIndexing(unittest.TestCase):
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
cnf(c3,axiom,q(Z,X)|~q(f(Z),X0)).
cnf(c4,axiom,p(X,X)|p(a,f(Y))).
cnf(c5,axiom,p(X,Y)|~q(b,a)|p(a,b)|~q(a,b)|p(Y,a)).
cnf(c6,axiom,~p(a,X)).
cnf(c7,axiom, q(f(a),a)).
cnf(c8,axiom, r(f(a))).
cnf(c9,axiom, p(X,Y)).
"""
        lex = Lexer(self.spec)
        self.c1 = clauses.parseClause(lex)
        self.c2 = clauses.parseClause(lex)
        self.c3 = clauses.parseClause(lex)
        self.c4 = clauses.parseClause(lex)
        self.c5 = clauses.parseClause(lex)
        self.c6 = clauses.parseClause(lex)
        self.c7 = clauses.parseClause(lex)
        self.c8 = clauses.parseClause(lex)
        self.c9 = clauses.parseClause(lex)

    def testResolutionInsertRemove(self):
        """
        Test inserting and removal of clauses into the resolution
        index.
        """
        index = ResolutionIndex()
        index.insertClause(self.c1)
        index.insertClause(self.c2)

        self.assertEqual(len(index.pos_idx), 1)
        self.assertEqual(len(index.pos_idx["p"]), 3)
        print(index.pos_idx)
        self.assertEqual(len(index.neg_idx), 1)
        self.assertEqual(len(index.neg_idx["p"]), 1)
        print(index.neg_idx)

        index.insertClause(self.c3)
        print("Insert ", self.c3)
        self.assertEqual(len(index.pos_idx), 2)
        self.assertEqual(len(index.pos_idx["p"]), 3)
        print(index.pos_idx)
        self.assertEqual(len(index.neg_idx), 2)
        self.assertEqual(len(index.neg_idx["p"]), 1)
        self.assertEqual(len(index.neg_idx["q"]), 1)
        self.assertEqual(len(index.pos_idx["q"]), 1)
        print(index.neg_idx)

        index.removeClause(self.c3)
        print("Removed ", self.c3)
        self.assertEqual(len(index.pos_idx), 2)
        self.assertEqual(len(index.pos_idx["p"]), 3)
        print(index.pos_idx)
        self.assertEqual(len(index.neg_idx), 2)
        self.assertEqual(len(index.neg_idx["p"]), 1)
        self.assertEqual(len(index.neg_idx["q"]), 0)
        self.assertEqual(len(index.pos_idx["q"]), 0)
        print(index.neg_idx)

    def testResolutionRetrieval(self):
        """
        Test actual retrieval of literal occurances from the index.
        """
        index = ResolutionIndex()
        index.insertClause(self.c1)
        index.insertClause(self.c2)
        index.insertClause(self.c3)
        index.insertClause(self.c4)
        index.insertClause(self.c5)

        print("testResolutionRetrieval()")
        lit = self.c6.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(len(cands), 8)
        for (c, i) in cands:
            lit = c.getLiteral(i)
            # self.assertEqual(lit.isNegative(), not lit.isNegative())
            self.assertEqual(termFunc(lit.atom), termFunc(lit.atom))

        lit = self.c7.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(len(cands), 3)
        for (c, i) in cands:
            lit = c.getLiteral(i)
            # self.assertEqual(lit.isNegative(), not lit.isNegative())
            self.assertEqual(termFunc(lit.atom), termFunc(lit.atom))

        lit = self.c8.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(cands, [])

    def testPredAbstraction(self):
        p1 = []
        p2 = [(True, "p")]
        p3 = [(True, "p"), (True, "p"), (True, "q")]
        p4 = [(False, "p"), (True, "p")]

        self.assertTrue(predAbstractionIsSubSequence(p1, p1))
        self.assertTrue(predAbstractionIsSubSequence(p2, p2))
        self.assertTrue(predAbstractionIsSubSequence(p3, p3))
        self.assertTrue(predAbstractionIsSubSequence(p4, p4))

        self.assertTrue(predAbstractionIsSubSequence(p1, p2))
        self.assertTrue(predAbstractionIsSubSequence(p1, p3))
        self.assertTrue(predAbstractionIsSubSequence(p1, p4))

        self.assertTrue(predAbstractionIsSubSequence(p2, p3))
        self.assertTrue(predAbstractionIsSubSequence(p2, p4))

        self.assertFalse(predAbstractionIsSubSequence(p2, p1))
        self.assertFalse(predAbstractionIsSubSequence(p3, p1))
        self.assertFalse(predAbstractionIsSubSequence(p4, p1))

        self.assertFalse(predAbstractionIsSubSequence(p3, p2))
        self.assertFalse(predAbstractionIsSubSequence(p4, p2))

        self.assertFalse(predAbstractionIsSubSequence(p3, p4))
        self.assertFalse(predAbstractionIsSubSequence(p4, p3))

    def testSubsumptionIndex(self):
        index = SubsumptionIndex()

        self.assertFalse(index.isIndexed(self.c1))
        self.assertFalse(index.isIndexed(self.c6))
        index.insertClause(self.c1)
        index.insertClause(self.c2)
        index.insertClause(self.c3)
        index.insertClause(self.c4)
        index.insertClause(self.c5)
        index.insertClause(self.c6)
        print(index.pred_abstr_arr)
        self.assertTrue(index.isIndexed(self.c1))
        self.assertTrue(index.isIndexed(self.c2))
        self.assertTrue(index.isIndexed(self.c3))
        self.assertTrue(index.isIndexed(self.c4))
        self.assertTrue(index.isIndexed(self.c5))
        self.assertTrue(index.isIndexed(self.c6))

        index.removeClause(self.c1)
        index.removeClause(self.c5)
        index.removeClause(self.c3)
        print(index.pred_abstr_arr)
        self.assertFalse(index.isIndexed(self.c1))
        self.assertTrue(index.isIndexed(self.c2))
        self.assertFalse(index.isIndexed(self.c3))
        self.assertTrue(index.isIndexed(self.c4))
        self.assertFalse(index.isIndexed(self.c5))
        self.assertTrue(index.isIndexed(self.c6))

        index.insertClause(self.c3)
        index.insertClause(self.c1)
        index.insertClause(self.c5)
        index.insertClause(self.c9)
        print(index.pred_abstr_arr)
        self.assertTrue(index.isIndexed(self.c1))
        self.assertTrue(index.isIndexed(self.c2))
        self.assertTrue(index.isIndexed(self.c3))
        self.assertTrue(index.isIndexed(self.c4))
        self.assertTrue(index.isIndexed(self.c5))
        self.assertTrue(index.isIndexed(self.c6))
        self.assertTrue(index.isIndexed(self.c9))

        cands = index.getSubsumingCandidates(self.c1)
        print(cands)
        self.assertEqual(len(cands), 3)
        cands = index.getSubsumingCandidates(self.c9)
        print(cands)
        self.assertEqual(len(cands), 1)

        cands = index.getSubsumedCandidates(self.c9)
        print(cands)
        self.assertEqual(len(cands), 5)

        cands = index.getSubsumedCandidates(self.c8)
        print(cands)
        self.assertEqual(len(cands), 0)

        cands = index.getSubsumedCandidates(self.c5)
        print(cands)
        self.assertEqual(len(cands), 1)
