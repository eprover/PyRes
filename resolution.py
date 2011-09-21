#!/usr/bin/env python2.7
# ----------------------------------
#
# Module resolution.py

"""
This module implements binary resolution, as given by the following
inference rule:

c1|a1     c2|~a2
---------------- where sigma=mgu(a1,a2)
 sigma(c1|c2)

Note that c1 and c2 are arbitrary disjunctions of literals, possibly
empty, and that a1 and a2 are atoms (so a1 and ~a2 are literals).


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
from lexer import Lexer
import substitutions
from unification import mgu
from literals import Literal
import clauses


def resolution(clause1, lit1, clause2, lit2):
    """
    Try to resolve clause1|lit1 against clause2|lit2. If this is
    possible, return the resolvent. Otherwise, return None.
    """
    l1 = clause1.getLiteral(lit1)
    l2 = clause2.getLiteral(lit2)
    if l1.isNegative() == l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    if sigma == None:
        return None
    lits1 = [l.instantiate(sigma) for l in clause1.literals if l!=l1]
    lits2 = [l.instantiate(sigma) for l in clause2.literals if l!=l2]
    lits1.extend(lits2)
    res = clauses.Clause(lits1)
    return res


class TestResolution(unittest.TestCase):
    """
    Unit test class for clauses. Test clause and literal
    functionality.
    """
    def setUp(self):
        """
        Setup function for resolution testing
        """
        print
        self.spec = """
cnf(c1,axiom,p(a, X)|p(X,a)).
cnf(c2,axiom,~p(a,b)|p(f(Y),a)).
cnf(c3,axiom,p(Z,X)|~p(f(Z),X0)).
"""
        lex = Lexer(self.spec)
        self.c1 = clauses.parseClause(lex)
        self.c2 = clauses.parseClause(lex)
        self.c3 = clauses.parseClause(lex)
       
    def testResolution(self):
        """
        Test resolution
        """
        res1 = resolution(self.c1, 0, self.c2,0)
        self.assert_(res1)
        print res1

        res2 = resolution(self.c1, 0, self.c3,0)
        self.assert_(not res2)
        print res2

        res3 = resolution(self.c2, 0, self.c3,0)
        self.assert_(res3)
        print res3

        res4 = resolution(self.c1, 0, self.c3,1)
        self.assert_(not res4)
        print res4


        
if __name__ == '__main__':
    unittest.main()
