#!/usr/bin/env python3
# ----------------------------------
#
# Module simplesat.py

"""
Minimalistic implementation of the given-clause algorithm for
saturation of clause sets under the rules of the resolution calculus.

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

from prover.clauses.clausesets import ClauseSet
from prover.proof.rescontrol import computeAllResolvents, computeAllFactors


class SimpleProofState(object):
    """
    Top-level data structure for the prover. The complete knowledge
    base is split into two sets, processed clauses and unprocessed
    clauses. These are represented here as individual clause sets. The
    main algorithm "processes" clauses and moves them from the
    unprocessed into the processed set. Processing typically generates
    several new clauses, which are direct consequences of the given
    clause and the processed claues. These new clauses are added to
    the set of unprocessed clauses.
    """
    def __init__(self, clauses):
        """
        Initialize the proof state with a set of clauses.
        """
        self.unprocessed = ClauseSet()                                    
        self.processed   = ClauseSet()
        for c in clauses.clauses:
            self.unprocessed.addClause(c)
        
    def processClause(self):
        """
        Pick a clause from unprocessed and process it. If the empty
        clause is found, return it. Otherwise return None.
        """
        given_clause = self.unprocessed.extractFirst()
        given_clause = given_clause.freshVarCopy()
        print("#", given_clause)
        if given_clause.isEmpty():
            # We have found an explicit contradiction
            return given_clause
        
        new = []
        factors    = computeAllFactors(given_clause)
        new.extend(factors)
        resolvents = computeAllResolvents(given_clause, self.processed)
        new.extend(resolvents)

        self.processed.addClause(given_clause)

        for c in new:
            self.unprocessed.addClause(c)
        return None

    def saturate(self):
        """
        Main proof procedure. If the clause set is found
        unsatisfiable, return the empty clause as a witness. Otherwise
        return None.
        """
        while self.unprocessed:
            res = self.processClause()
            if res != None:
                return res
        else:
            return None

