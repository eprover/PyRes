#!/usr/bin/env python3
# ----------------------------------
#
# Module subsumption.py

"""
This module implements first-order subsumption, as defined by the
simplification rule below:

Subsumption:

 C|R    D
=========== if sigma(D)=C for some substitution sigma
     D

Note that C, D, R (and hence C|R) are clauses, i.e. they are
multi-sets of literals interpreted as disjunctions. The multi-set
aspect is important for this particular calculus, otherwise
p(X)|p(Y) would be able to subsume p(X), i.e. a clause would subsume
its own factors. This would destroy completeness.

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
from lexer import Lexer
from substitutions import BTSubst
from matching import match
from literals import Literal
from clauses import Clause, parseClause
from clausesets import ClauseSet

def subsumeLitLists(subsumer, subsumed, subst):
    """
    Try to extend subst so that subst(subsumer) is a multi-subset of
    subsumed.
    """
    if not subsumer:
        return True
    for lit in subsumed:
        btstate = subst.getState()
        if subsumer[0].match(lit, subst):
            rest = [l for l in subsumed if l != lit]
            if subsumeLitLists(subsumer[1:], rest, subst):
                return True
        subst.backtrackToState(btstate)
    return False

def subsumes(subsumer, subsumed):
    """
    Return True if subsumer subsumes subsumed, False otherwise.
    """
    if len(subsumer) > len(subsumed):
        return False
    subst = BTSubst()
    subsumer_list = subsumer.literals
    subsumed_list = subsumed.literals
    return subsumeLitLists(subsumer_list, subsumed_list, subst)

def forwardSubsumption(set, clause):
    """
    Return True if any clause from set subsumes clause, False otherwise.
    """
    candidates = set.getSubsumingCandidates(clause)
    for c in candidates:
        if subsumes(c, clause):
            return True
    return False


def backwardSubsumption(clause, set):
    """
    Remove all clauses that are subsumed by clause from set.
    """
    candidates = set.getSubsumedCandidates(clause)
    subsumed_set = []
    for c in candidates:
        if subsumes(clause, c):
            subsumed_set.append(c)
    res = len(subsumed_set)
    for c in subsumed_set:
        set.extractClause(c)
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

        res = subsumes(self.c4, self.c4)
        self.assertTrue(res)

        res = subsumes(self.c1, self.c2)
        self.assertTrue(res)

        res = subsumes(self.c2, self.c1)
        self.assertTrue(not res)

        res = subsumes(self.c2, self.c3)
        self.assertTrue(not res)

        res = subsumes(self.c3, self.c2)
        self.assertTrue(res)

        res = subsumes(self.c4, self.c5)
        self.assertTrue(res)

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


if __name__ == '__main__':
    unittest.main()
