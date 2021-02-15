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
import errno
import os
import os.path

from lexer import Lexer, Token
from signature import Signature
from clauses import Clause, parseClause
from clausesets import ClauseSet
from formulas import WFormula, parseWFormula, negateConjecture
from formulacnf import wFormulaClausify
from eqaxioms import generateEquivAxioms, generateCompatAxioms

def tptpLexer(source, refdir):
    """
    Create a lexer for reading a file using the TPTP convention. If
    refdir exists, interpret name relative to it. If this does not
    exist, interpret it relative to $TPTP. Return lexer, new refdir.
    """
    lex = None

    if not refdir:
        refdir = os.getcwd()

    name = os.path.join(refdir, source)
    try:
        fp = open(name, "r")
        lex = Lexer(fp.read())
        fp.close()
        refdir = os.path.dirname(name)
    except IOError:
        tptp = os.getenv("TPTP")
        if tptp:
            name = os.path.join(tptp, source)
            fp = open(name, "r")
            lex = Lexer(fp.read())
            fp.close()
            refdir = os.path.dirname(name)
        else:
            raise IOError(errno.ENOENT, "File not found", name)
    return lex, refdir



class FOFSpec(object):
    """
    A datastructure for representing a mixed set of clauses and
    formulas, with support for clausification of the clauses.
    """

    def __init__(self):
        """
        Initialize the specification.
        """
        self.clauses  = []
        self.formulas = []
        self.isFof    = False
        self.hasConj  = False

    def __repr__(self):
        """
        Return a string representation of the spec.
        """
        res= "\n".join([repr(c) for c in self.clauses]+
                       [repr(f) for f in self.formulas])
        return res

    def addClause(self,clause):
        """
        Add a clause to the specification.
        """
        if clause.type == "negated_conjecture":
            self.hasConj = True
        self.clauses.append(clause)

    def addFormula(self,formula):
        """
        Add a clause to the specification.
        """
        if formula.type in ["conjecture", "negated_conjecture"] :
            self.hasConj = True
        self.isFof = True
        self.formulas.append(formula)

    def parse(self, source, refdir=None):
        """
        Parse a mixed FOF/CNF specification with includes. "source" is
        either a filename or a lexer initialized with the input
        text. "refdir" is the reference directory for TPTP includes.
        """

        if not isinstance(source, Lexer):
            source, refdir = tptpLexer(source, refdir)

        while not source.TestTok(Token.EOFToken):
            source.CheckLit(["cnf", "fof", "include"])
            if source.TestLit("cnf"):
                clause = parseClause(source)
                self.addClause(clause)
            elif source.TestLit("fof"):
                formula = parseWFormula(source)
                self.addFormula(formula)
            else:
                source.AcceptLit("include")
                source.AcceptTok(Token.OpenPar)
                name = source.LookLit()[1:-1]
                source.AcceptTok(Token.SQString)
                source.AcceptTok(Token.ClosePar)
                source.AcceptTok(Token.FullStop)
                self.parse(name, refdir)

    def clausify(self):
        """
        Convert all formulas in the spec into clauses, add them to
        self.clauses, and return the resulting set of all clauses.
        """
        while self.formulas:
            form = self.formulas.pop()
            form = negateConjecture(form)
            tmp = wFormulaClausify(form)
            self.clauses.extend(tmp)

        return ClauseSet(self.clauses)

    def addEqAxioms(self):
        """
        Add equality axioms (if necessary). Return True if equality
        is present, false otherwise.
        """
        sig = Signature()
        for c in self.clauses:
            c.collectSig(sig)

        for f in self.formulas:
            f.collectSig(sig)

        if sig.isPred("="):
            res = generateEquivAxioms()
            res.extend(generateCompatAxioms(sig))
            self.clauses.extend(res)
            return True
        return False


# ------------------------------------------------------------------
#                  Unit test section
# ------------------------------------------------------------------

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


if __name__ == '__main__':
    unittest.main()
