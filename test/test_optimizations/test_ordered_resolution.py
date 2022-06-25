#!/usr/bin/env python3
# ----------------------------------
#
# Module orderedResolution.py

"""

"""
import unittest

from prover.clauses.clauses import parseClause
from prover.optimizations.ordered_resolution import *


class TestOrderedResolution(unittest.TestCase):
    """
    Test basic functions
    """

    def setUp(self):
        self.input1 = "cnf(c96,plain,butler!=X264|X266!=X265|hates(X264,X265)|~hates(agatha,X266))."
        lex = Lexer(self.input1)
        self.given_clause = parseClause(lex)
        self.ocb = OCBCell()

    def testselectInferenceLitsOrderedResolution(self):
        for lit in self.given_clause.literals:
            self.ocb.insert2dic(lit.atom)
        selectInferenceLitsOrderedResolution(self.ocb, self.given_clause)
        self.assertEqual(self.given_clause.literals[0].inference_lit, False)
        self.assertEqual(self.given_clause.literals[1].inference_lit, True)
        self.assertEqual(self.given_clause.literals[2].inference_lit, False)
        self.assertEqual(self.given_clause.literals[3].inference_lit, True)


if __name__ == '__main__':
    unittest.main()
