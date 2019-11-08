#!/usr/bin/env python3
# ----------------------------------
#
# Module eqaxioms.py

"""
Equality is a central relation in automated deduction. The simplest
way of handling equality is to add axioms describing its
properties. In this way, any calculus that is complete for first-order
logic can be applied to proof problems with equality. 

Equality is a congruence relation, i.e. it is an equivalence relation
that is compatible with the term structure. As an equivalence
relation, it has to conform the the axioms of reflexivity, symmetry,
and transitivity. These can be written as follows:

Reflexivity:  ![X]:X=X
Symmetry:     ![X,Y]:(X=Y -> Y=X)
Transitivity: ![X,Y,Z]:((X=Y & Y=Z) -> X=Z)

The compatibility property requires that we can replace "equals with
equals". The need to be stated for each function symbol and each
predicate symbols in the problem:

Assume f|n in F, i.e. f is s function symbol of arity n. Then
![X1,...,Xn,Y1,...,Yn]:((X1=Y1 & ... & Xn=Yn)->f(X1,...,Xn)=f(Y1,...,Yn))
describes the compatibility of the equality relation (=) with f.

Assume p|n in P. Then
![X1,...,Xn,Y1,...,Yn]:((X1=Y1 & ... & Xn=Yn)->(p(X1,...Xn)->p(Y1,...Yn)))
describes the compatibility of the equality relation with p. Note that
we do not need to specify the symmetric case p(X1,...Xn)<-p(Y1,...Yn)
because it follows from the contrapositive (~p(Y1,...Yn)->~p(X1,...Xn)
and the symmetry of equality.
[* Make easier *]

The axioms can be directly converted into clausal logic, yielding:

X=X
X!=Y | Y=X
X!=Y | Y!=Z | X=Z

X1!=Y1|...|Xn!=Yn|f(X1,...,Xn)=f(Y1,...Yn) for all f|n in F.
X1!=Y1|...|Xn!=Yn|~p(X1,...Xn)|p(Y1,...,Yn) for all p|n in P.


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
from lexer import Token,Lexer
from derivations import Derivable,Derivation
from signature import Signature
from terms import *
from literals import Literal
from clauses import Clause,parseClause


def generateEquivAxioms():
    """
    Return a list with the three axioms describing an equivalence
    relation. We are lazy here...
    """
    lex = Lexer("""
    cnf(reflexivity, axiom, X=X).
    cnf(symmetry, axiom, X!=Y|Y=X).
    cnf(transitivity, axiom, X!=Y|Y!=Z|X=Z).
    """)
    res = []
    while not lex.TestTok(Token.EOFToken):
        c = parseClause(lex)
        c.setDerivation(Derivation("eq_axiom"))
        res.append(c)
    return res


def generateVarList(x, n):
    """
    Generate a list of variables of the form x1,...,xn, where x is any
    string, and n is >= 0.
    """
    return [x+"%d"%(i) for i in range(1,n+1)]
    

def generateEqPremise(arity):
    """
    Generate a list of literals of the form
    X1!=Y1|...|Xn!=Yn.
    """
    res = [Literal(list(["=", vars[0],vars[1]]), True) for vars in
    zip(generateVarList("X", arity), generateVarList("Y",arity))]
    return res
    

def generateFunCompatAx(f, arity):
    """
    Generate axioms for the form
    X1!=Y1|...|Xn!=Yn|f(X1,...,Xn)=f(Y1,...Yn)    
    for f with the given arity.
    """
    res = generateEqPremise(arity)
    lterm = list([f])
    lterm.extend(generateVarList("X",arity))
    rterm = list([f])
    rterm.extend(generateVarList("Y",arity))
    concl = Literal(["=", lterm, rterm], False)
    res.append(concl)

    resclause = Clause(res)
    resclause.setDerivation(Derivation("eq_axiom"))
    return resclause
    

def generatePredCompatAx(p, arity):
    """
    Generate axioms for the form
    X1!=Y1|...|Xn!=Yn|~p(X1,...,Xn)|p(Y1,...Yn)    
    for f with the given arity.
    """
    res = generateEqPremise(arity)

    negp = list([p])
    negp.extend(generateVarList("X",arity))
    res.append(Literal(negp, True))

    posp = list([p])
    posp.extend(generateVarList("Y",arity))
    res.append(Literal(posp, False))
    
    resclause = Clause(res)
    resclause.setDerivation(Derivation("eq_axiom"))
    return resclause


def generateCompatAxioms(sig):
    """
    Given a signature, generate and return all the compatibility
    axioms. 
    """
    res = []
    for f in sig.funs:
        arity = sig.getArity(f)
        if arity>0:
            c = generateFunCompatAx(f, arity)
            res.append(c)

    for p in sig.preds:
        arity = sig.getArity(p)
        if arity>0 and p!="=":
            c = generatePredCompatAx(p, arity)
            res.append(c)

    return res


# ------------------------------------------------------------------
#                  Unit test section
# ------------------------------------------------------------------

class TestEqAxioms(unittest.TestCase):
    """
    Test cases for equality axiom generation.
    """
    def setUp(self):
        """
        """
        print()
        
       
    def testEquivAxioms(self):
        """
        Test that the equivalence axioms are generated (or at least
        provide coverage ;-).
        """
        ax = generateEquivAxioms()
        print(ax)
        self.assertEqual(len(ax), 3)

    def testVarStuff(self):
        """
        Test variable and premise generation.
        """
        vars = generateVarList("X", 4)
        self.assertTrue("X1" in vars)
        self.assertTrue("X4" in vars)
        self.assertTrue(not "X5" in vars)
        self.assertTrue(not "Y1" in vars)
        self.assertEqual(len(vars), 4)
        print(vars)

        lits = generateEqPremise(3)
        self.assertEqual(len(lits), 3)
        print(lits)

    def testCompatibility(self):
        """
        Test that compatibility axioms are generated as expected.
        """
        ax = generateFunCompatAx("f", 3)
        self.assertEqual(len(ax),4)
        print(ax)

        ax = generatePredCompatAx("p", 5)
        self.assertEqual(len(ax),7)
        print(ax)

        sig = Signature()
        sig.addFun("f", 2)
        sig.addPred("p", 3)
        sig.addFun("a", 0)

        tmp = generateCompatAxioms(sig)
        # Note: No axiom for a
        self.assertEqual(len(tmp), 2)


if __name__ == '__main__':
    unittest.main()
