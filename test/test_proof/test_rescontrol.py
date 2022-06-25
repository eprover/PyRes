#!/usr/bin/env python3
# ----------------------------------
#
# Module rescontrol.py

"""
Functions wrapping basic inference rules for convenience.


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

from prover.clauses.clauses import parseClause
from prover.clauses.clausesets import ClauseSet
from prover.parser.lexer import Lexer
from prover.proof.rescontrol import *


class TestSetInferences(unittest.TestCase):
    """
    Unit test class for simple resolution inference control.
    """

    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        spec = """
cnf(g1, negated_conjecture, ~c).
cnf(c1, axiom, a|b|c).
cnf(c2, axiom, b|c).
cnf(c3, axiom, c).
"""
        lex = Lexer(spec)
        self.conj = parseClause(lex)
        self.cset = ClauseSet()
        self.cset.parse(lex)

        cstr = "cnf(ftest, axiom, p(X)|~q|p(a)|~q|p(Y))."
        lex = Lexer(cstr)
        self.fclause = parseClause(lex)

    def testSetResolution(self):
        """
        Test that forming resolvents between a clause and a clause set
        works.
        """
        print("Test set resolution")
        res = computeAllResolvents(self.conj, self.cset)
        print(res)

    def testFactoring(self):
        """
        Test full factoring of a clause.
        """
        print("Test factoring")
        res = computeAllFactors(self.fclause)
        print(res)


if __name__ == '__main__':
    unittest.main()
