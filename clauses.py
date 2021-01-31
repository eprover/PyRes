#!/usr/bin/env python3
# ----------------------------------
#
# Module clause.py

"""
A simple implementation of first-order clauses.

See literals.py for the definition of atoms and literals.

A logical clause in our sense is a multi-set of literals, implicitly
representing the universally quantified disjunction of these literals.

The set of all clauses for a given signature is denoted as
Clauses(P,F,V).

We represent a clause as a list of literals. The actual clause data
structure contains additional information that is useful, but not
strictly necessary from a logic/alculus point of view.


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
from lexer import Token,Lexer
from derivations import Derivable,Derivation
from signature import Signature

from terms import *
import substitutions
from literals import Literal, parseLiteral, parseLiteralList,\
     literalList2String, litInLitList, oppositeInLitList
from litselection import firstLit, varSizeLit, eqResVarSizeLit



class Clause(Derivable):
    """
    A class representing a clause. A clause at the moment comprises
    the following elements:
    - The literal list.
    - The type ("plain" if none given)
    - The name (generated automatically if not given)
    """
    def __init__(self, literals, type="plain", name=None):
        """
        Initialize the clause.
        """
        self.literals   = [l for l in literals if not l.isPropFalse()]
        self.type       = type
        self.evaluation = None
        Derivable.__init__(self, name)


    def __repr__(self):
        """
        Return a string representation of the clause.
        """
        res = "cnf(%s,%s,%s%s)."%(self.name, self.type,\
                                  literalList2String(self.literals),\
                                  self.strDerivation())
        if self.evaluation:
            res = res+"/* %s */"%(repr(self.evaluation),)
        return res

    def __len__(self):
        """
        Return the number of literals in the clause.
        """
        return len(self.literals)

    def isEmpty(self):
        """
        Return true if the clause is empty.
        """
        return len(self.literals) == 0

    def isUnit(self):
        """
        Return true if the clause is a unit clause.
        """
        return len(self.literals) == 1

    def isHorn(self):
        """
        Return true if the clause is a Horn clause.
        """
        tmp = [l for l in self.literals if l.isPositive()]
        return len(tmp) <= 1

    def getLiteral(self, position):
        """
        Return the indicated literal of the clause. Position is an
        integer from 0 to litNumber (exclusive).
        """
        assert position >= 0
        assert position < len(self)
        return self.literals[position]

    def getNegativeLits(self):
        """
        Return a list of all negative literals in the clause.
        """
        return [l for l in self.literals if l.isNegative()]

    def collectVars(self, res=None):
        """
        Insert all variables in self into the set res and return
        it. If res is not given, create it.
        """
        if not res:
            res = set([])
        for i in self.literals:
            res = i.collectVars(res)
        return res

    def collectSig(self, sig=None):
        """
        Collect function- and predicate symbols into the signature. If
        none exists, create it. Return the signature
        """
        if not sig:
            sig = Signature()

        for i in self.literals:
            i.collectSig(sig)
        return sig


    def weight(self, fweight, vweight):
        """
        Return the symbol-count weight of the clause.
        """
        res = 0
        for l in self.literals:
            res = res + l.weight(fweight, vweight)
        return res

    def selectInferenceLits(self, lit_selection_fun=firstLit):
        """
        Perform negative literal selection. lit_selection_function is
        a function that takes a list of literals and returns a sublist
        of literals (normally of length 1) that should be selected.
        """
        candidates = self.getNegativeLits()
        if not candidates:
            return
        # print("Got: ", candidates)

        for l in self.literals:
            l.setInferenceLit(False)

        selected = lit_selection_fun(candidates)
        for l in selected:
            l.setInferenceLit(True)

    def predicateAbstraction(self):
        """
        The predicate abstraction of a clause is an ordered tuple of
        the predicate abstractions of its literals. As an example, the
        predicate abstraction of p(x)|~q(Y)|q(a) would be
        ((False, q), (True, p), (True, q)) (assuming True > False and
        q > p). We will use this later to implement a simple
        subsumption index.
        """
        res = [l.predicateAbstraction() for l in self.literals]
        res.sort()
        return tuple(res)


    def instantiate(self, subst):
        """
        Return an instantiated copy of self. Name and type are copied
        and need to be overwritten if that is not desired.
        """
        lits = [l.instantiate(subst) for l in self.literals]
        res = Clause(lits, self.type, self.name)
        res.setDerivation(self.derivation)
        return res

    def freshVarCopy(self):
        """
        Return a copy of self with fresh variables.
        """
        vars  = self.collectVars()
        subst = substitutions.freshVarSubst(vars)
        return self.instantiate(subst)

    def addEval(self, eval):
        """
        Add an evaluation to the clause. "eval" is an ordered list of
        numerical evaluations, one for each of the different
        evaluation functions used.
        """
        self.evaluation = eval

    def removeDupLits(self):
        """
        Remove duplicated literals from clause.
        """
        res = []
        for l in self.literals:
            if not litInLitList(l,res):
                res.append(l)
        self.literals = res

    def isTautology(self):
        """
        Check if a clause is a simple tautology, i.e. if it contains
        two literals with the same atom, but different signs.
        """
        for i in range(len(self.literals)):
            if oppositeInLitList(self.literals[i],
                                 self.literals[i+1:]):
                return True
        return False



def parseClause(lexer):
    """
    Parse a clause. A clause in (slightly simplified) TPTP-3 syntax is
    written as
       cnf(<name>, <type>, <literal list>).
    where <name> is a lower-case ident, type is a lower-case ident
    from a specific list, and <literal list> is a "|" separated list
    of literals, optionally enclosed in parenthesis.

    For us, all clause types are essentially the same, so we only
    distinguish "axiom", "negated_conjecture", and map everything else
    to "plain".
    """
    lexer.AcceptLit("cnf");
    lexer.AcceptTok(Token.OpenPar)
    name = lexer.LookLit()
    lexer.AcceptTok(Token.IdentLower)
    lexer.AcceptTok(Token.Comma)
    type = lexer.LookLit()
    if not type in ["axiom", "negated_conjecture"]:
        type = "plain"
    lexer.AcceptTok(Token.IdentLower)
    lexer.AcceptTok(Token.Comma)
    if lexer.TestTok(Token.OpenPar):
        lexer.AcceptTok(Token.OpenPar)
        lits = parseLiteralList(lexer)
        lexer.AcceptTok(Token.ClosePar)
    else:
        lits = parseLiteralList(lexer)
    lexer.AcceptTok(Token.ClosePar)
    lexer.AcceptTok(Token.FullStop)

    res = Clause(lits, type, name)
    res.setDerivation(Derivation("input"))
    return res



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

        self.assertEqual(cf.weight(2,1), c1.weight(2,1))
        self.assertEqual(cf.weight(1,1), c1.weight(1,1))

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
        self.assertTrue(len(c5)<oldlen)


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
        for l in c2.literals:
            self.assertTrue(l.isInferenceLit())

        c3.selectInferenceLits()
        for l in c3.literals:
            self.assertEqual(l.isNegative(), l.isInferenceLit())


        c2.selectInferenceLits(varSizeLit)
        for l in c2.literals:
            self.assertTrue(l.isInferenceLit())

        c3.selectInferenceLits(varSizeLit)
        for l in c3.literals:
            self.assertEqual(l.isNegative(), l.isInferenceLit())

        self.assertEqual(c1.predicateAbstraction(), ((True, "p"), (True, "p")))
        self.assertEqual(c2.predicateAbstraction(), ((True, "p"), (True, "p")))
        self.assertEqual(c3.predicateAbstraction(), ((False, "p"), (True, "p")))


if __name__ == '__main__':
    unittest.main()
