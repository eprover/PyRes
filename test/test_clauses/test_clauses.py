"""
Copyright 2010-2021 Stephan Schulz, schulz@eprover.org

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

from prover.clauses.clauses import parseClause, Clause
from prover.optimizations.litselection import firstLit, varSizeLit
from prover.optimizations.ocb import OCBCell
from prover.clauses.terms import *


class TestClauses(unittest.TestCase):
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
        self.str1 = """
cnf(test,axiom,p(a)|p(f(X))).
cnf(test,axiom,(p(a)|p(f(X)))).
cnf(test3,lemma,(p(a)|~p(f(X)))).
cnf(taut,axiom,p(a)|q(a)|~p(a)).
cnf(dup,axiom,p(a)|q(a)|p(a)).
"""

    def testClauses(self):
        """
        Test that basic literal parsing works correctly.
        """
        lex = Lexer(self.str1)
        c1 = parseClause(lex)
        c2 = parseClause(lex)
        c3 = parseClause(lex)
        c4 = parseClause(lex)
        c5 = parseClause(lex)

        print(c1)
        print(c2)
        self.assertEqual(repr(c1), repr(c2))

        cf = c1.freshVarCopy()
        print(c1)
        print(cf)

        self.assertEqual(cf.weight(2, 1), c1.weight(2, 1))
        self.assertEqual(cf.weight(1, 1), c1.weight(1, 1))

        cnew = Clause(c4.literals)
        self.assertTrue(cnew.getLiteral(0).isEqual(c4.getLiteral(0)))

        empty = Clause([])
        self.assertTrue(empty.isEmpty())
        self.assertTrue(not empty.isUnit())
        self.assertTrue(empty.isHorn())

        unit = Clause([c5.getLiteral(0)])
        self.assertTrue(not unit.isEmpty())
        self.assertTrue(unit.isUnit())
        self.assertTrue(unit.isHorn())

        self.assertTrue(not c1.isHorn())
        self.assertTrue(c3.isHorn())

        self.assertTrue(c4.isTautology())
        self.assertTrue(not c5.isTautology())

        oldlen = len(c5)
        c5.removeDupLits()
        self.assertTrue(len(c5) < oldlen)

        sig = c1.collectSig()
        c2.collectSig(sig)
        c3.collectSig(sig)
        c4.collectSig(sig)
        c5.collectSig(sig)
        print(sig)

        negs = c1.getNegativeLits()
        self.assertEqual(len(negs), 0)
        negs = c2.getNegativeLits()
        self.assertEqual(len(negs), 0)
        negs = c3.getNegativeLits()
        self.assertEqual(len(negs), 1)
        negs = c4.getNegativeLits()
        self.assertEqual(len(negs), 1)
        negs = c5.getNegativeLits()
        self.assertEqual(len(negs), 0)

        c2.selectInferenceLits()
        for lit in c2.literals:
            self.assertTrue(lit.isInferenceLit())

        c3.selectInferenceLits()
        for lit in c3.literals:
            self.assertEqual(lit.isNegative(), lit.isInferenceLit())

        c2.selectInferenceLits(varSizeLit)
        for lit in c2.literals:
            self.assertTrue(lit.isInferenceLit())

        c3.selectInferenceLits(varSizeLit)
        for lit in c3.literals:
            self.assertEqual(lit.isNegative(), lit.isInferenceLit())

        self.assertEqual(c1.predicateAbstraction(), ((True, "p"), (True, "p")))
        self.assertEqual(c2.predicateAbstraction(), ((True, "p"), (True, "p")))
        self.assertEqual(c3.predicateAbstraction(), ((False, "p"), (True, "p")))

        # check ordered resolution + neglitselection
        ocb = OCBCell()
        for lit in c1.literals:
            ocb.insert2dic(lit.atom)
        c1.selectInferenceLits(firstLit, ocb)
        self.assertTrue(not c1.literals[0].isInferenceLit())
        self.assertTrue(c1.literals[1].isInferenceLit())
        for lit in c4.literals:
            ocb.insert2dic(lit.atom)
        c5.selectInferenceLits(firstLit, ocb)
        self.assertTrue(not c5.literals[0].isInferenceLit())
        self.assertTrue(c5.literals[1].isInferenceLit())
