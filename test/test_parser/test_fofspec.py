#!/usr/bin/env python3
# ----------------------------------
#
# Module fofspec.py

"""
This module implements parsing and processing for full first-order
logic, in mixed TPTP FOF and CNF format.

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

from prover.parser.fofspec import FOFSpec
from prover.parser.lexer import Lexer


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

        self.seed = """
        cnf(agatha,plain,lives(agatha)).
        cnf(butler,plain,lives(butler)).
        cnf(charles,plain,lives(charles)).
        include('includetest.txt').
        """
        inctext = """
        fof(dt_m1_filter_2,axiom,(
        ! [A] :
        ( ( ~ v3_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
        => ! [B] :
        ( m1_filter_2(B,A)
        => ( ~ v1_xboole_0(B)
        & m2_lattice4(B,A) ) ) ) )).
        """
        fp = open("includetest.txt", "w")
        fp.write(inctext)
        fp.close()

        self.testeq = """
        cnf(clause, axiom, a=b).
        fof(eqab, axiom, a=b).
        fof(pa, axiom, p(a)).
        fof(fb, axiom, ![X]:f(X)=b).
        fof(pa, conjecture, ?[X]:p(f(X))).
        """

    def testParse(self):
        """
        Test the parsing and printing of a FOF spec.
        """

        lex = Lexer(self.seed)
        spec = FOFSpec()

        spec.parse(lex)
        print("MIX:\n===")
        print(spec)

    def testCNF(self):
        """
        Test CNFization.
        """

        lex = Lexer(self.seed)
        spec = FOFSpec()
        spec.parse(lex)
        spec.clausify()
        print("CNF:\n===")
        print(spec)

    def testEqAxioms(self):
        """
        Test equality handling.
        """
        lex = Lexer(self.testeq)
        spec = FOFSpec()
        spec.parse(lex)

        spec.addEqAxioms()

        print("EQ:\n===")
        print(spec)
