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
from prover.proof import substitutions
from prover.clauses.derivations import Derivable
from prover.clauses.literals import litInLitList, oppositeInLitList
from prover.clauses.conversion import literalList2String
from prover.optimizations.litselection import firstLit
from prover.optimizations.ordered_resolution import selectInferenceLitsOrderedResolution
from prover.clauses.terms import *


class Clause(Derivable):
    """
    A class representing a clause. A clause at the moment comprises
    the following elements:
    - The literal list.
    - The type ("plain" if none given)
    - The name (generated automatically if not given)

    Optionally a clause can compromise following elements:
    - A list of evaulation of the clause
    - A flag that inidicated if the clause is part of the Set-Of-Support (SOS)
    """

    def __init__(self, literals, clause_type="plain", name=None):
        """
        Initialize the clause.
        """
        self.literals = [lit for lit in literals if not lit.isPropFalse()]
        self.type = clause_type
        self.evaluation = None
        self.part_of_sos = False
        Derivable.__init__(self, name)

    def __repr__(self):
        """
        Return a string representation of the clause.
        """
        res = "cnf(%s,%s,%s%s)." % (self.name, self.type,
                                    literalList2String(self.literals),
                                    self.strDerivation())
        if self.evaluation:
            res = res + "/* %s */" % (repr(self.evaluation))
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
        tmp = [lit for lit in self.literals if lit.isPositive()]
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
        return [lit for lit in self.literals if lit.isNegative()]

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
        for lit in self.literals:
            res = res + lit.weight(fweight, vweight)
        return res

    def selectInferenceLits(self, lit_selection_fun=firstLit, ocb=None):
        """
        Perform negative literal selection. lit_selection_function is
        a function that takes a list of literals and returns a sublist
        of literals (normally of length 1) that should be selected.
        """
        candidates = self.getNegativeLits()
        if not candidates:
            if ocb is not None:  # negLitSelection and ordered Resolution
                selectInferenceLitsOrderedResolution(ocb, self)
            return
        # print("Got: ", candidates)
        for lit in self.literals:
            lit.setInferenceLit(False)

        selected = lit_selection_fun(candidates)
        for lit in selected:
            lit.setInferenceLit(True)

    def predicateAbstraction(self):
        """
        The predicate abstraction of a clause is an ordered tuple of
        the predicate abstractions of its literals. As an example, the
        predicate abstraction of p(x)|~q(Y)|q(a) would be
        ((False, q), (True, p), (True, q)) (assuming True > False and
        q > p). We will use this later to implement a simple
        subsumption index.
        """
        res = [lit.predicateAbstraction() for lit in self.literals]
        res.sort()
        return tuple(res)

    def instantiate(self, subst):
        """
        Return an instantiated copy of self. Name and type are copied
        and need to be overwritten if that is not desired.
        """
        lits = [lit.instantiate(subst) for lit in self.literals]
        res = Clause(lits, self.type, self.name)
        res.setDerivation(self.derivation)
        res.part_of_sos = self.part_of_sos
        return res

    def freshVarCopy(self):
        """
        Return a copy of self with fresh variables.
        """
        variables = self.collectVars()
        subst = substitutions.freshVarSubst(variables)
        return self.instantiate(subst)

    def addEval(self, evaluation):
        """
        Add an evaluation to the clause. "eval" is an ordered list of
        numerical evaluations, one for each of the different
        evaluation functions used.
        """
        self.evaluation = evaluation

    def removeDupLits(self):
        """
        Remove duplicated literals from clause.
        """
        res = []
        for lit in self.literals:
            if not litInLitList(lit, res):
                res.append(lit)
        self.literals = res

    def isTautology(self):
        """
        Check if a clause is a simple tautology, i.e. if it contains
        two literals with the same atom, but different signs.
        """
        for i in range(len(self.literals)):
            if oppositeInLitList(self.literals[i],
                                 self.literals[i + 1:]):
                return True
        return False


