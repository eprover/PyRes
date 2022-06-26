"""
Implementation of the given-clause algorithm for saturation of clause
sets under the rules of the resolution calculus. This improves on the
very basic implementation in simplesat in several ways.

- It supports heuristic clause selection, not just first-in first-out
- It supports tautology deletion
- It supports forward and backwards subsumption
- It keeps some statistics to enable the user to understand the
  practical impact of different steps of the algorithm better.

Most of these changes can be found in the function processClause() of
the ProofState class.

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

from prover.clauses.clausesets import ClauseSet, HeuristicClauseSet, IndexedClauseSet
from prover.optimizations import heuristics
from prover.optimizations.ordered_resolution import selectInferenceLitsOrderedResolution, countsymbols, initocb
from prover.optimizations.setofsupport import NoSos
from prover.optimizations.subsumption import forwardSubsumption, backwardSubsumption
from prover.proof.rescontrol import computeAllResolvents, computeAllFactors


class SearchParams(object):
    """
    A simple container for different parameter settings for the proof
    search.
    """

    def __init__(self,
                 heuristics=heuristics.PickGiven5,
                 delete_tautologies=False,
                 forward_subsumption=False,
                 backward_subsumption=False,
                 literal_selection=None,
                 ordered_resolution=False,
                 sos_strategy=NoSos()):
        """
        Initialize heuristic parameters.
        """
        self.heuristics = heuristics
        """
        This defines the clause selection heuristic, i.e. the order in
        which uprocessed clauses are selected for processing.
        """
        self.delete_tautologies = delete_tautologies
        """
        This determines if tautologies will be deleted. Tautologies in
        plain first-order logic (without equality) are clauses which
        contain two literals with the same atom, but opposite signs.
        """
        self.forward_subsumption = forward_subsumption
        """
        Forward-subsumption checks the given clause against already
        processed clauses, and discards it if it is subsumed.
        """
        self.backward_subsumption = backward_subsumption
        """
        Backwars subsumption checks the processed clauses against the
        given clause, and discards all processed clauses that are
        subsumed.
        """
        self.literal_selection = literal_selection
        """
        Either None, or a function that selects a subset of negative
        literals from a set of negative literals (both represented as
        lists, not Python sets) as the inference literal.
        """
        self.ordered_resolution = ordered_resolution
        """
        Use KBO ordered Resolution or not.
        """
        self.sos_strategy = sos_strategy
        """
        Either None, or a reference to a class that is able to divide the
        clause set into a base set and a set-of-support.
        """


class ProofState(object):
    """
    Top-level data structure for the prover. The complete knowledge
    base is split into two sets, processed clauses and unprocessed
    clauses. These are represented here as individual clause sets. The
    main algorithm "processes" clauses and moves them from the
    unprocessed into the processed set. Processing typically generates
    several new clauses, which are direct consequences of the given
    clause and the processed claues. These new clauses are added to
    the set of unprocessed clauses.

    In addition to the clause sets, this data structure also maintains
    a number of counters for statistics on the proof search.
    """

    def __init__(self, params, clauses, silent=False, indexed=False):
        """
        Initialize the proof state with a set of clauses.
        """
        self.params = params
        self.unprocessed = HeuristicClauseSet(params.heuristics, params.sos_strategy)

        if indexed:
            self.processed = IndexedClauseSet()
        else:
            self.processed = ClauseSet()
        for c in clauses.clauses:
            self.unprocessed.addClause(c)
        self.initial_clause_count = len(self.unprocessed)
        self.proc_clause_count = 0
        self.factor_count = 0
        self.resolvent_count = 0
        self.tautologies_deleted = 0
        self.forward_subsumed = 0
        self.backward_subsumed = 0
        self.silent = silent

        if self.params.ordered_resolution:  # if ordered resolution init ocb and count the symbols
            option = self.params.ordered_resolution
            self.symbol_count = countsymbols(clauses)
            self.ocb = initocb(self.symbol_count, option)

    def processClause(self):
        """
        Pick a clause from unprocessed and process it. If the empty
        clause is found, return it. Otherwise return None.
        """
        given_clause = self.unprocessed.extractBest()
        given_clause = given_clause.freshVarCopy()
        if not self.silent:
            print("#")
        if given_clause.isEmpty():
            # We have found an explicit contradiction
            return given_clause
        if self.params.delete_tautologies and \
                given_clause.isTautology():
            self.tautologies_deleted += 1
            return None
        if self.params.forward_subsumption and \
                forwardSubsumption(self.processed, given_clause):
            # If the given clause is subsumed by an already processed
            # clause, all releveant inferences will already have been
            # done with that more general clause. So we can discard
            # the given clause. We do keep count of how many clauses
            # we have dropped this way.
            self.forward_subsumed += 1
            return None

        if self.params.backward_subsumption:
            # If the given clause subsumes any of the already
            # processed clauses, it will "cover" for these less
            # general clauses in the future, so we can remove them
            # from the proof state. Again, we keep count of the number
            # of clauses dropped. This typically happens less often
            # than forward subsumption, because most heuristics prefer
            # smaller clauses, which tend to be more general (thus the
            # processed clauses are typically if not universally more
            # general than the new given clause).
            tmp = backwardSubsumption(given_clause, self.processed)
            self.backward_subsumed = self.backward_subsumed + tmp
        if self.params.ordered_resolution and self.params.literal_selection:
            given_clause.selectInferenceLits(self.params.literal_selection, self.ocb)
        elif self.params.literal_selection:
            given_clause.selectInferenceLits(self.params.literal_selection)
        elif self.params.ordered_resolution:
            selectInferenceLitsOrderedResolution(self.ocb, given_clause)

        if not self.silent:
            print("#", given_clause)
        new = []
        factors = computeAllFactors(given_clause)
        new.extend(factors)
        resolvents = computeAllResolvents(given_clause, self.processed)
        new.extend(resolvents)
        self.proc_clause_count = self.proc_clause_count + 1
        self.factor_count = self.factor_count + len(factors)
        self.resolvent_count = self.resolvent_count + len(resolvents)

        self.processed.addClause(given_clause)

        for c in new:
            self.unprocessed.addClause(c)
        return None

    def init_sos(self):
        num_sos_clauses = self.params.sos_strategy.mark_sos(self.unprocessed)
        self.unprocessed.num_sos_clauses += num_sos_clauses

        if self.params.sos_strategy.ratio == 0 and self.unprocessed.num_sos_clauses > 0:
            non_sos_clauses = []
            for clause in self.unprocessed.clauses:
                if clause.part_of_sos is False:
                    non_sos_clauses.append(clause)

            for clause in non_sos_clauses:
                self.unprocessed.extractClause(clause)
                self.processed.addClause(clause)

    def saturate(self):
        """
        Main proof procedure. If the clause set is found
        unsatisfiable, return the empty clause as a witness. Otherwise
        return None.
        """
        self.init_sos()

        while self.unprocessed:
            res = self.processClause()
            if res is not None:
                return res
        else:
            return None

    def statisticsStr(self):
        """
        Return the proof state statistics in string form ready for
        output.
        """
        return """
# Initial clauses    : %d
# Processed clauses  : %d
# Factors computed   : %d
# Resolvents computed: %d
# Tautologies deleted: %d
# Forward subsumed   : %d
# Backward subsumed  : %d""" \
               % (self.initial_clause_count,
                  self.proc_clause_count,
                  self.factor_count,
                  self.resolvent_count,
                  self.tautologies_deleted,
                  self.forward_subsumed,
                  self.backward_subsumed)
