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

from prover.clauses.clauses import parseClause
from prover.clauses.clausesets import ClauseSet
from prover.parser.lexer import Lexer
from prover.proof.substitutions import BTSubst


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
            rest = [lit for lit in subsumed if lit != lit]
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
