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
from lexer import Token,Lexer
from resolution import resolution, factor
from clauses import parseClause
from clausesets import ClauseSet


def computeAllResolvents(clause, clauseset):
    """
    Compute all binary resolvents between a given clause and all
    clauses in clauseset.

    In the "given-clause algorithm", the proof state is represented by
    two sets of clauses, the set of _processed_ clauses, and the set
    of _unprocessed_ clauses. Originally, all clauses are
    unprocessed. The main invariant is that at all times, all the
    generating inferences between processed clauses have been computed
    and added to the proof state. The algorithm moves one clause at a
    time from unprocessed, and adds it to processed (unless the clause
    is redundant).

    This function  is used when integrating a new clause into the
    processed part of the proof state. It computes all the resolvents
    between a single clause (the new "given clause") and a clause set
    (the _processed clauses_). These clauses need to be added to the
    proof state to maintain the invariant. Since they are new, they
    will be added to the set of unprocessed clauses.
    """
    res = []
    for lit in range(len(clause)):
        if clause.getLiteral(lit).isInferenceLit():
            partners = \
                     clauseset.getResolutionLiterals(clause.getLiteral(lit))
            for (cl2, lit2) in partners:
                resolvent = resolution(clause, lit, cl2, lit2)
                if resolvent!=None:
                    res.append(resolvent)
    return res


def computeAllFactors(clause):
    """
    Compute all (direct) factors of clause. This operation is O(n^2)
    if n is the number of literals. However, factoring is nearly never
    a critical operation. Single-clause operations are nearly always
    much cheaper than clause/clause-set operations.
    """
    res = []
    for i in range(len(clause)):
        for j in range(i+1, len(clause)):
            if clause.getLiteral(i).isInferenceLit() or \
               clause.getLiteral(j).isInferenceLit():
                fact = factor(clause, i, j)
                if fact:
                    res.append(fact)
    return res


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
        lex  = Lexer(spec)
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
