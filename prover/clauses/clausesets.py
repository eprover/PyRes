"""
Clause sets for maintaining sets of clauses, possibly sorted by
heuristical evaluation.

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

from prover.parser.parser import parseClause
from prover.clauses.signature import Signature
from prover.optimizations.indexing import ResolutionIndex, SubsumptionIndex
from prover.optimizations.setofsupport import NoSos


class ClauseSet(object):
    """
    A class representing a clause set (or, more precisely,
    a multi-set of clauses).
    """

    def __init__(self, clauses=None):
        """
        Initialize the clause.
        """
        if clauses is None:
            clauses = []
        self.clauses = list(clauses)

    def __repr__(self):
        """
        Return a string representation of the clause set.
        """
        return "\n".join([repr(clause) for clause in self.clauses])

    def __len__(self):
        """
        Return number of clauses in set.
        """
        return len(self.clauses)

    def addClause(self, clause):
        """
        Add a clause to the clause set.
        """
        self.clauses.append(clause)

    def extractClause(self, clause):
        """
        Remove a clause to the clause set and return it.
        """
        self.clauses.remove(clause)
        return clause

    def collectSig(self, sig=None):
        """
        Collect function- and predicate symbols into the signature. If
        none exists, create it. Return the signature
        """
        if not sig:
            sig = Signature()

        for i in self.clauses:
            i.collectSig(sig)
        return sig

    def extractFirst(self):
        """
        Extract and return the first clause.
        """
        if self.clauses:
            clause = self.clauses.pop(0)
            return clause
        else:
            return None

    def getResolutionLiterals(self, lit):
        """
        Return a list of tuples (clause, literal-index) such that the
        set includes at least all literals that can potentially be
        resolved against lit. In the naive and obviously correct first
        implementation, this simply returns a list of all
        literal-indices for all clauses.
        """
        res = [(c, i) for c in self.clauses for i in range(len(c)) if
               c.getLiteral(i).isInferenceLit()]
        return res

    def getSubsumingCandidates(self, queryclause):
        """
        Return a subset (as a list) of the set containing at least all
        clauses potentially subsuming queryclause. For a plain
        ClauseSet, we just return all clauses in the set. 
        """
        return self.clauses

    def getSubsumedCandidates(self, queryclause):
        """
        Return a subset (as a list) of the set containing at least the
        clauses  potentially subsumed by queryclause). For a plain
        ClauseSet, we just return all clauses in the set.
        """
        return self.clauses

    def parse(self, lexer):
        """
        Parse a sequence of clauses from lex and add them to the
        set. Return number of clauses parsed.
        """
        count = 0
        while lexer.LookLit() == "cnf":
            clause = parseClause(lexer)
            self.addClause(clause)
            count = count + 1
        return count


class HeuristicClauseSet(ClauseSet):
    """
    A class representing a clause set (or, more precisely, a multi-set
    of clauses) with heuristic evaluations.

    All clauses inserted into the set are evaluated
    according to all criteria. The clause set support extraction of
    the "best" clause according to any of the configured heuristics.
    """

    def __init__(self, eval_functions, sos_strategy=None):
        """
        Initialize the clause.
        """
        super().__init__()
        self.clauses = []
        self.eval_functions = eval_functions
        self.sos_strategy = sos_strategy if sos_strategy is not None else NoSos()
        self.num_sos_clauses = 0

    def addClause(self, clause):
        """
        Add a clause to the clause set. If the clause set supports
        heuristic evaluations, add the relevant evaluations to the
        clause.
        """
        evals = self.eval_functions.evaluate(clause)
        clause.addEval(evals)
        if clause.part_of_sos:
            self.num_sos_clauses += 1
        ClauseSet.addClause(self, clause)

    def extractBestByEval(self, heuristic_index, clause_of_sos=False):
        """
        Find and return the clause with the lowest weight according
        to the selected heuristic. If the set is empty, return None.

        The method also considers the parameter part_of_sos. If the parameter is True
        the method will only return a clause that is part of sos. If it is False
        the method will only return a clause that is not part of sos.
        If no clause matches the sos requirement it will return None.
        """
        if self.clauses:
            best = -1
            besteval = float('inf')

            for i in range(0, len(self.clauses)):
                if self.clauses[i].evaluation[heuristic_index] < besteval \
                        and self.clauses[i].part_of_sos == clause_of_sos:
                    besteval = self.clauses[i].evaluation[heuristic_index]
                    best = i
            if best == -1:
                return None
            else:
                if clause_of_sos:
                    self.num_sos_clauses -= 1
                return self.clauses.pop(best)

    def extractBest(self):
        """
        Extract and return the next "best" clause according to the
        evaluation scheme.
        """
        # determines which of the evaluation metrics should be applied (lowest index or least literals)
        heuristic_index = self.eval_functions.nextEval()

        # determines whether the clause should or should not be part of the set of support
        if not self.constains_sos_clauses():
            clause_of_sos = False
        elif self.contains_only_sos_clauses():
            clause_of_sos = True
        else:
            clause_of_sos = self.sos_strategy.should_apply()

        return self.extractBestByEval(heuristic_index, clause_of_sos)

    def constains_sos_clauses(self):
        return self.num_sos_clauses > 0

    def contains_only_sos_clauses(self):
        return len(self.clauses) == self.num_sos_clauses


class IndexedClauseSet(ClauseSet):
    """
    This is a normal clause set, augmented by indices that speeds up
    the finding of resolution and subsumption partners.
    """

    def __init__(self, clauses=None):
        """
        Create the two indices and call the superclass initializer. 
        """
        if clauses is None:
            clauses = []
        self.res_index = ResolutionIndex()
        self.sub_index = SubsumptionIndex()
        ClauseSet.__init__(self, clauses)

    def addClause(self, clause):
        """
        Add the clause to the indices, then use the  superclass
        function to add it to the actual set.
        """
        self.res_index.insertClause(clause)
        self.sub_index.insertClause(clause)
        ClauseSet.addClause(self, clause)

    def extractClause(self, clause):
        """
        Remove the clause from the indices, then use the  superclass
        function to remove it to the actual set.
        """
        self.res_index.removeClause(clause)
        self.sub_index.removeClause(clause)
        return ClauseSet.extractClause(self, clause)

    def getResolutionLiterals(self, lit):
        """
        Overwrite the original function with one based on indexing. 
        """
        return self.res_index.getResolutionLiterals(lit)

    def getSubsumingCandidates(self, queryclause):
        """
        Overwrite the original function with one based on indexing. 
        """
        return self.sub_index.getSubsumingCandidates(queryclause)

    def getSubsumedCandidates(self, queryclause):
        """
        Overwrite the original function with one based on indexing. 
        """
        return self.sub_index.getSubsumedCandidates(queryclause)
