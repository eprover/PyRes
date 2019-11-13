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
        if not topsymbol in idx:
            idx[topsymbol] = set()
        idx[topsymbol].add(payload)

    def removeData(self, idx, topsymbol, payload):        
        idx[topsymbol].remove(payload)
        
    def insertClause(self, clause):
        for i in range(len(clause)):
            lit = clause.getLiteral(i)
            if lit.isInferenceLit():
                if lit.isPositive():
                    self.insertData(self.pos_idx, termFunc(lit.atom), (clause, i))
                else:
                    self.insertData(self.neg_idx, termFunc(lit.atom), (clause, i))

    def removeClause(self, clause):
        for i in range(len(clause)):
            lit = clause.getLiteral(i)
            if lit.isInferenceLit():
                if lit.isPositive():
                    self.removeData(self.pos_idx, termFunc(lit.atom), (clause, i))
                else:
                    self.removeData(self.neg_idx, termFunc(lit.atom), (clause, i))

    def getResolutionLiterals(self, lit):
        if lit.isPositive():
            idx = self.neg_idx
        else:
            idx = self.pos_idx
        try:
            return list(idx[termFunc(lit.atom)])
        except KeyError:
            return list()
                    

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
cnf(c5,axiom,p(X)|~q(b)|p(a)|~q(a)|p(Y)).
cnf(c6,axiom,~p(a)).
cnf(c7,axiom, q(f(a))).
cnf(c8,axiom, r(f(a))).
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
        
        lit = self.c6.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertTrue(len(cands), 7)
        for (c,i) in cands:
            l = c.getLiteral(i)
            self.assertEqual(l.isNegative(), not lit.isNegative())
            self.assertEqual(termFunc(l.atom), termFunc(lit.atom))
            
        lit = self.c7.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertTrue(len(cands), 3)
        for (c,i) in cands:
            l = c.getLiteral(i)
            self.assertEqual(l.isNegative(), not lit.isNegative())
            self.assertEqual(termFunc(l.atom), termFunc(lit.atom))

        lit = self.c8.getLiteral(0)
        cands = index.getResolutionLiterals(lit)
        print(cands)
        self.assertEqual(cands, [])

            
if __name__ == '__main__':
    unittest.main()
