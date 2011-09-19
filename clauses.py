#!/usr/bin/env python2.7
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
strictly necessary from a clogic/alculus point of view.


Copyright 2010-2011 Stephan Schulz, schulz@eprover.org

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
Hirschstrasse 35
76133 Karlsruhe
Germany
Email: schulz@eprover.org
"""

import unittest
from lexer import Token,Lexer
from terms import *
import substitutions
from literals import Literal, parseLiteral, parseLiteralList, literalList2String


class Clause(object):
    """
    A class representing a clause. A clause at the moment comprises
    the following elements:
    - The literal list.
    - The type ("plain" if none given)
    - The name (generated automatically if not given)
    """
    clauseIdCounter = 0
    """
    Counter for generating new clause names.
    """
        
    def __init__(self, literals, type="plain", name=None):
        """
        Initialize the clause.
        """
        self.literals   = literals
        self.type       = type
        self.setName(name)
        self.evaluation = None
        
    def __repr__(self):
        """
        Return a string representation of the clause.
        """
        return "cnf(%s,%s,%s)."%(self.name, self.type, literalList2String(self.literals))

    def setName(self, name = None):
        """
        Set the name. If no name is given, generate a default name.
        """
        if name:
            self.name = name
        else:
            name = "c%d"%(Clause.clauseIdCounter,)
            Clause.clauseIdCounter = Clause.clauseIdCounter+1        

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
        return len(self.literals) <= 1

    def litNumber(self):
        """
        Return the number of literals in the clause.
        """
        return len(self.literals)

    def getLiteral(self, position):
        """
        Return the indicated literal of the clause. Position is an
        integer from 0 to litNumber (exclusive).
        """
        assert position >= 0
        assert position < self.litNumber()
        return self.literals[position]

    def collectVars(self, res=None):
        """
        Insert all variables in self into the set res and return
        it. If res is not given, create it.
        """
        for i in self.literals:
            res = i.collectVars(res)
        return res

    def weight(self, fweight, vweight):
        """
        Return the symbol-count weight of the clause.
        """
        res = 0
        for l in self.literals:
            res = res + l.weight(fweight, vweight)
        return res

    def instantiate(self, subst):
        """
        Return an instantiated copy of self. Name and type are copied
        and need to be overwritten if that is not desired.
        """
        lits = [l.instantiate(subst) for l in self.literals]
        return Clause(lits, self.type, self.name)

    def freshVarCopy(self):
        """
        Return a copy of self with fresh variables.
        """
        vars  = self.collectVars()
        subst = substitutions.freshVarSubst(vars)
        return self.instantiate(subst)

    def addEval(self, eval):
        """
        Add an evaluation to the clause.
        """
        self.evaluation = eval
   

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
    if not type in ["axiom", "negated conjecture"]:
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

    return Clause(lits, type, name)


    

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
        print
        self.str1 = """
cnf(test,axiom,p(a)|p(f(X))).
cnf(test,axiom,(p(a)|p(f(X)))).
cnf(test3,lemma,(p(a)|~p(f(X))))."""
       
    def testClauses(self):
        """
        Test that basic literal parsing works correctly.
        """
        lex = Lexer(self.str1)
        c1 = parseClause(lex)
        c2 = parseClause(lex)
        c3 = parseClause(lex)

        print c1
        print c2
        self.assertEqual(repr(c1), repr(c2))

        c4 = c1.freshVarCopy()
        print c1
        print c4

        self.assertEqual(c4.weight(2,1), c1.weight(2,1))
        self.assertEqual(c4.weight(1,1), c1.weight(1,1))

        c5 = Clause(c4.literals)
        self.assert_(c5.getLiteral(0).isEqual(c4.getLiteral(0)))

        empty = Clause([])
        self.assert_(empty.isEmpty())
        self.assert_(not empty.isUnit())
        self.assert_(empty.isHorn())

        unit = Clause([c5.getLiteral(0)])
        self.assert_(not unit.isEmpty())
        self.assert_(unit.isUnit())
        self.assert_(unit.isHorn())

        self.assert_(not c1.isHorn())
        self.assert_(not c3.isHorn())
        
if __name__ == '__main__':
    unittest.main()
