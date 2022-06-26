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

from prover.optimizations.subsumption import *
from prover.parser.lexer import Lexer
from prover.parser.parser import parseClause


class TestSubsumption(unittest.TestCase):
    """
    Unit test class for subsumption. """

    def setUp(self):
        """
        Setup function for subsumption testing
        """
        print()
        self.spec = """
cnf(axiom, c1, $false).
cnf(axiom, c2, p(a)).
cnf(axiom, c3, p(X)).
cnf(axiom, c4, p(a)|q(f(X))).
cnf(axiom, c5, p(a)|q(f(b))|p(X)).
cnf(axiom, c6, X=X).
cnf(axiom, c7, Y=Y).
"""
        lex = Lexer(self.spec)
        self.c1 = parseClause(lex)
        self.c2 = parseClause(lex)
        self.c3 = parseClause(lex)
        self.c4 = parseClause(lex)
        self.c5 = parseClause(lex)
        self.c6 = parseClause(lex)
        self.c7 = parseClause(lex)

        self.cset = ClauseSet()
        self.cset.addClause(self.c2)
        self.cset.addClause(self.c3)
        self.cset.addClause(self.c4)
        self.cset.addClause(self.c5)
        self.cset.addClause(self.c6)
        self.cset.addClause(self.c7)

    def testSubsumption(self):
        """
        Test subsumption.
        """
        res = subsumes(self.c1, self.c1)
        self.assertTrue(res)

        res = subsumes(self.c2, self.c2)
        self.assertTrue(res)

        res = subsumes(self.c3, self.c3)
        self.assertTrue(res)

        # res = subsumes(self.c4, self.c4)
        # self.assertTrue(res)

        res = subsumes(self.c1, self.c2)
        self.assertTrue(res)

        res = subsumes(self.c2, self.c1)
        self.assertTrue(not res)

        res = subsumes(self.c2, self.c3)
        self.assertTrue(not res)

        res = subsumes(self.c3, self.c2)
        self.assertTrue(res)

        # res = subsumes(self.c4, self.c5)
        # self.assertTrue(res)

        res = subsumes(self.c5, self.c4)
        self.assertTrue(not res)

        res = subsumes(self.c6, self.c6)
        self.assertTrue(res)

        res = subsumes(self.c6, self.c7)
        self.assertTrue(res)

    def testSetSubsumption(self):
        """
        Test set subsumption.
        """
        self.assertTrue(not forwardSubsumption(self.cset, self.c1))
        self.assertTrue(forwardSubsumption(self.cset, self.c2))

        tmp = backwardSubsumption(self.c1, self.cset)
        self.assertEqual(tmp, 6)

