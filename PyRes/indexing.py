#!/usr/bin/env python3
# ----------------------------------
#
# Module indexing.py

"""
In general, an index is a data structure that allows us to reasonably
efficiently retrieve items from a set of data items that are in a
defined relation with a query item.

In theorem proving, we use indexing to find suitable inference
partners for a clause. There are many different indexing techniques
with different strengths and weaknesses. Two of the more important
classifications are term indexes vs. clause indexes, and perfect
indexes vs. non-perfect indexes.

As the name suggests, a term index indexes terms (or, since the
strucure is the same, atoms) - although it often indexes clauses via
(some of) the terms that occur in it. Typical retrieval relations are
identity, match (for a query term t, find all terms s for which a
substitution sigma exists such that sigma(s)=t), instance (for a query
term t, find all terms s for which a substitution sigma exists such
that s=sigma(t), and unifiability (find all terms with a sigma such
that sigma(s)=sigma(t).

Clause indexed directly index clauses, typically by abstracting a
clause into some kind of sequential vector. Typical retrieval
relations are subsumption (both ways).

Perfect indexes return exactly the terms in the given retrieval
relation (somtimes along with the substitution, if any). Non-perfect
indices return a superset of candidates, on which the actual
relationship still needs to be tested. Perfect indexes have the
advantage that no extra tests are necessary, but non-perfect indexes
are often simpler to implement and more efficient to maintain.

Here we are implementing an non-perfect index that returns potential
resolution partners. Given an inference literal l (in one clause), the
index returns a set of pairs (c, i), where c is a clause and i is the
position of a potential inference literal, so that l and c[i] have
diffent polarity and the underlying atoms are potentially
unifiable. The indexing technique used is called "top symbol hashing",
and it assumes two terms (or atoms) are potentially unifiable if they
share the same top symbol.


Copyright 2019 Stephan Schulz, schulz@eprover.org

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
from terms import termFunc
from literals import Literal
import clauses


class ResolutionIndex(object):
    """
    This class implements a simple index that can return resolution
    candidates (a set of clause and literal index pairs) for a given
    query literal. The returned literal occurances have the opposite
    polarity of the query literal and the same top symbol (i.e. we
    implement a simple version of top symbol hashing).
    """
    def __init__(self):
        """
        We use separate dicts for mapping predicate symbols to
        positive literal occurances and negative literal occurances.
        """
        self.pos_idx = {}
        self.neg_idx = {}


    def insertData(self, idx, topsymbol, payload):
        """
        Insert the payload into the provided index, associating it
        with the given top symbol (i.e. the predicate symbol of the
        indexed literal). The payload here is a tuple (clause, pos),
        where pos is the position of the indexed literal in the clause
        (counting from 0).
        """
        if not topsymbol in idx:
            idx[topsymbol] = set()
        idx[topsymbol].add(payload)

    def removeData(self, idx, topsymbol, payload):
        """
        Remove a payload indexed at topsymbol from the provided
        index.
        """
        idx[topsymbol].remove(payload)

    def insertClause(self, clause):
        """
        Insert all inference literals of clause into the appropriate
        index (positive or negative, depending on the sign of the
        literal).
        """
        for i in range(len(clause)):
            lit = clause.getLiteral(i)
            if lit.isInferenceLit():
                if lit.isPositive():
                    self.insertData(self.pos_idx, termFunc(lit.atom), (clause, i))
                else:
                    self.insertData(self.neg_idx, termFunc(lit.atom), (clause, i))

    def removeClause(self, clause):
        """
        Remove all inference literals of the clause from the index.
        """
        for i in range(len(clause)):
            lit = clause.getLiteral(i)
            if lit.isInferenceLit():
                if lit.isPositive():
                    self.removeData(self.pos_idx, termFunc(lit.atom), (clause, i))
                else:
                    self.removeData(self.neg_idx, termFunc(lit.atom), (clause, i))

    def getResolutionLiterals(self, lit):
        """
        Return a list of resolution candidates for lit. Every
        candidate is a pair (clause, pos), where pos is the position
        of the literal that potentially unifies with lit (and has the
        opposite sign).
        """
        if lit.isPositive():
            idx = self.neg_idx
        else:
            idx = self.pos_idx
        try:
            return list(idx[termFunc(lit.atom)])
        except KeyError:
            return list()

def predAbstractionIsSubSequence(candidate, superseq):
    """
    Check if candidate is a subsequence of superseq. That is a
    necessary condition for the clause that produced candidate to
    subsume the clause that produced superseq.
    """
    i = 0
    end = len(superseq)
    try:
        for la in candidate:
            while superseq[i]!=la:
                i = i+1
            i = i+1
    except IndexError:
        return False
    return True


class SubsumptionIndex(object):
    """
    This class implements a simple index to speed up subsumption. This
    is based on the predicate abstraction of a clause. The index
    organises clauses by there predicate abstraction. Since we know
    that a clause C can only subsume a clause c if C's predicate
    abstraction is a subset of c's predicate abstraction, we can
    exclude whole sets of clauses at once.
    """
    def __init__(self):
        """
        We store predicate abstractions (with associated clauses) in a
        dictionary for for fast access by abstraction. We also store
        them in an array sorted by length, so that we only need to
        consider stored clauses that are short enough to have a chance
        to subsume.
        """
        self.pred_abstr_set = {}
        self.pred_abstr_arr = []

    def insertClause(self, clause):
        """
        Insert a clause into the index. If the predicate abstraction
        already is stored, just add the clause to the associated set
        of clauses. Otherwise, create a new entry for the pa and add
        the clause.
        """
        pa = clause.predicateAbstraction()

        try:
            entry =  self.pred_abstr_set[pa]
        except KeyError:
            entry = set()
            self.pred_abstr_set[pa] = entry
            l = len(pa)
            i = 0
            for (len_pa, spa, clauses) in self.pred_abstr_arr:
                if len_pa >= l:
                    break
                i = i+1
            self.pred_abstr_arr.insert(i, (l, pa, entry))

        entry.add(clause)

    def removeClause(self, clause):
        """
        Remove a clause. This is easy, since we never remove the entry
        for the predicate abstraction, only the clause from its
        set. In general, successful backward subsumption is rare, so
        deletion of a processed clause will be rare, too.
        """
        pa = clause.predicateAbstraction()
        entry = self.pred_abstr_set[pa]
        entry.remove(clause)

    def isIndexed(self, clause):
        """
        Return True if a clause is in the index. At the moment, this
        is only used for unit tests.
        """
        pa = clause.predicateAbstraction()

        try:
            entry =  self.pred_abstr_set[pa]
            return clause in entry
        except KeyError:
            return False

    def getSubsumingCandidates(self, queryclause):
        """
        Return a list of all clauses that can potentially subsume the
        query. This goes through the relevant part of the list of
        predicate abstractions and collects the clauses stored with
        predicate abstractions compatible with subsumption.
        """
        pa = queryclause.predicateAbstraction()
        pa_len = len(pa)
        res = list()
        for (cpa_len, cpa, clauses) in self.pred_abstr_arr:
            if cpa_len > pa_len:
                break
            if predAbstractionIsSubSequence(cpa, pa):
                res.extend(clauses)
        return res

    def getSubsumedCandidates(self, queryclause):
        """
        Return a list of all clauses that can potentially be subsumed
        by query. See previous function
        """
        pa = queryclause.predicateAbstraction()
        pa_len = len(pa)
        res = list()
        for (cpa_len, cpa, clauses) in self.pred_abstr_arr:
            if cpa_len < pa_len:
                continue
            if predAbstractionIsSubSequence(pa, cpa):
                res.extend(clauses)
        return res


class TestIndexing(unittest.TestCase):
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
cnf(c1,axiom,p(a, X)|p(X,a)).
cnf(c2,axiom,~p(a,b)|p(f(Y),a)).
cnf(c3,axiom,q(Z,X)|~q(f(Z),X0)).
cnf(c4,axiom,p(X,X)|p(a,f(Y))).
cnf(c5,axiom,p(X,Y)|~q(b,a)|p(a,b)|~q(a,b)|p(Y,a)).
cnf(c6,axiom,~p(a,X)).
cnf(c7,axiom, q(f(a),a)).
cnf(c8,axiom, r(f(a))).
cnf(c9,axiom, p(X,Y)).
"""
        lex = Lexer(self.spec)
        self.c1 = clauses.parseClause(lex)
        self.c2 = clauses.parseClause(lex)
        self.c3 = clauses.parseClause(lex)
        self.c4 = clauses.parseClause(lex)
        self.c5 = clauses.parseClause(lex)
        self.c6 = clauses.parseClause(lex)
        self.c7 = clauses.parseClause(lex)
        self.c8 = clauses.parseClause(lex)
        self.c9 = clauses.parseClause(lex)

    def testResolutionInsertRemove(self):
        """
        Test inserting and removal of clauses into the resolution
        index.
        """
        index = ResolutionIndex()
        index.insertClause(self.c1)
        index.insertClause(self.c2)

        self.assertEqual(len(index.pos_idx), 1)
        self.assertEqual(len(index.pos_idx["p"]), 3)
        print(index.pos_idx)
        self.assertEqual(len(index.neg_idx), 1)
        self.assertEqual(len(index.neg_idx["p"]), 1)
        print(index.neg_idx)

        index.insertClause(self.c3)
        print("Insert ", self.c3)
        self.assertEqual(len(index.pos_idx), 2)
        self.assertEqual(len(index.pos_idx["p"]), 3)
        print(index.pos_idx)
        self.assertEqual(len(index.neg_idx), 2)
        self.assertEqual(len(index.neg_idx["p"]), 1)
        self.assertEqual(len(index.neg_idx["q"]), 1)
        self.assertEqual(len(index.pos_idx["q"]), 1)
        print(index.neg_idx)

        index.removeClause(self.c3)
        print("Removed ", self.c3)
        self.assertEqual(len(index.pos_idx), 2)
        self.assertEqual(len(index.pos_idx["p"]), 3)
        print(index.pos_idx)
        self.assertEqual(len(index.neg_idx), 2)
        self.assertEqual(len(index.neg_idx["p"]), 1)
        self.assertEqual(len(index.neg_idx["q"]), 0)
        self.assertEqual(len(index.pos_idx["q"]), 0)
        print(index.neg_idx)

    def testResolutionRetrieval(self):
        """
        Test actual retrieval of literal occurances from the index.
        """
        index = ResolutionIndex()
        index.insertClause(self.c1)
        index.insertClause(self.c2)
        index.insertClause(self.c3)
        index.insertClause(self.c4)
        index.insertClause(self.c5)

        print("testResolutionRetrieval()")
        lit = self.c6.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(len(cands), 8)
        for (c,i) in cands:
            l = c.getLiteral(i)
            self.assertEqual(l.isNegative(), not lit.isNegative())
            self.assertEqual(termFunc(l.atom), termFunc(lit.atom))

        lit = self.c7.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(len(cands), 3)
        for (c,i) in cands:
            l = c.getLiteral(i)
            self.assertEqual(l.isNegative(), not lit.isNegative())
            self.assertEqual(termFunc(l.atom), termFunc(lit.atom))

        lit = self.c8.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(cands, [])

    def testPredAbstraction(self):
        p1 = []
        p2 = [(True, "p")]
        p3 = [(True, "p"), (True, "p"), (True, "q")]
        p4 = [(False, "p"), (True, "p")]

        self.assertTrue(predAbstractionIsSubSequence(p1, p1))
        self.assertTrue(predAbstractionIsSubSequence(p2, p2))
        self.assertTrue(predAbstractionIsSubSequence(p3, p3))
        self.assertTrue(predAbstractionIsSubSequence(p4, p4))

        self.assertTrue(predAbstractionIsSubSequence(p1, p2))
        self.assertTrue(predAbstractionIsSubSequence(p1, p3))
        self.assertTrue(predAbstractionIsSubSequence(p1, p4))

        self.assertTrue(predAbstractionIsSubSequence(p2, p3))
        self.assertTrue(predAbstractionIsSubSequence(p2, p4))

        self.assertFalse(predAbstractionIsSubSequence(p2, p1))
        self.assertFalse(predAbstractionIsSubSequence(p3, p1))
        self.assertFalse(predAbstractionIsSubSequence(p4, p1))

        self.assertFalse(predAbstractionIsSubSequence(p3, p2))
        self.assertFalse(predAbstractionIsSubSequence(p4, p2))

        self.assertFalse(predAbstractionIsSubSequence(p3, p4))
        self.assertFalse(predAbstractionIsSubSequence(p4, p3))

    def testSubsumptionIndex(self):
        index = SubsumptionIndex()

        self.assertFalse(index.isIndexed(self.c1))
        self.assertFalse(index.isIndexed(self.c6))
        index.insertClause(self.c1)
        index.insertClause(self.c2)
        index.insertClause(self.c3)
        index.insertClause(self.c4)
        index.insertClause(self.c5)
        index.insertClause(self.c6)
        print(index.pred_abstr_arr)
        self.assertTrue(index.isIndexed(self.c1))
        self.assertTrue(index.isIndexed(self.c2))
        self.assertTrue(index.isIndexed(self.c3))
        self.assertTrue(index.isIndexed(self.c4))
        self.assertTrue(index.isIndexed(self.c5))
        self.assertTrue(index.isIndexed(self.c6))

        index.removeClause(self.c1)
        index.removeClause(self.c5)
        index.removeClause(self.c3)
        print(index.pred_abstr_arr)
        self.assertFalse(index.isIndexed(self.c1))
        self.assertTrue(index.isIndexed(self.c2))
        self.assertFalse(index.isIndexed(self.c3))
        self.assertTrue(index.isIndexed(self.c4))
        self.assertFalse(index.isIndexed(self.c5))
        self.assertTrue(index.isIndexed(self.c6))

        index.insertClause(self.c3)
        index.insertClause(self.c1)
        index.insertClause(self.c5)
        index.insertClause(self.c9)
        print(index.pred_abstr_arr)
        self.assertTrue(index.isIndexed(self.c1))
        self.assertTrue(index.isIndexed(self.c2))
        self.assertTrue(index.isIndexed(self.c3))
        self.assertTrue(index.isIndexed(self.c4))
        self.assertTrue(index.isIndexed(self.c5))
        self.assertTrue(index.isIndexed(self.c6))
        self.assertTrue(index.isIndexed(self.c9))

        cands = index.getSubsumingCandidates(self.c1)
        print(cands)
        self.assertEqual(len(cands), 3)
        cands = index.getSubsumingCandidates(self.c9)
        print(cands)
        self.assertEqual(len(cands), 1)

        cands = index.getSubsumedCandidates(self.c9)
        print(cands)
        self.assertEqual(len(cands), 5)

        cands = index.getSubsumedCandidates(self.c8)
        print(cands)
        self.assertEqual(len(cands), 0)

        cands = index.getSubsumedCandidates(self.c5)
        print(cands)
        self.assertEqual(len(cands), 1)


if __name__ == '__main__':
    unittest.main()
