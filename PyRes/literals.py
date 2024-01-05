#!/usr/bin/env python3
# ----------------------------------
#
# Module literal.py

"""
A simple implementation of first-order atoms and literals.

We assume a set of function symbols F (with associated arities) and
variables symbols as defined in terms.py. We now also assume a set P
of predicate symbols, and extend the arity function to
ar:F \cup P ->N

The set of all first-order atoms over P, F, V, Atom(P,F,V) is defined
as follows:
- If t1, ... t_n are in Term(F,V) and p|n is in P, then p(t1,..., tn)
  is in Atom(P,F,V)
- Atom(P,F,V) is the smallest set with this property.


Assume F={f|2, g|1, a|0, b|0}, V={X, Y, ...} and P={p|1, q|2}. Then
the following are atoms:

p(a)
q(X, g(g(a)))
p(f(b, Y))

Because of the special role of equality for theorem proving, we
usually assume "="|2 and "!="|2 are in P. In the concrete syntax,
these symbols are written as infix symbols, i.e. we write a=b, not
"=(a, b)".

A literal is a signed atom. A positive literal is syntactically
identical to its atom. A negative literal consists of the negation
sign, ~, followed by an atom.

Thus, we can describe the set
Literals(P,F,V) = {~a | a in Atom(P,F,V)} \cup Atom(P,F,V)

We establish the convention that t1!=t2 is equivalent to ~t1=t2 and
~t1!=t2 is equivalent to t1=t2, and only use the respective later
forms internally. In other words, the symbol != only occurs during
parsing and printing.


Copyright 2010-2020 Stephan Schulz, schulz@eprover.org

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
from signature import Signature
from terms import *
from substitutions import BTSubst
from matching import match



def parseAtom(lexer):
    """
    Parse an atom. An atom is either a conventional atom, in which
    case it's syntactically identical to a term, or it is an
    equational literal, of the form 't1=t2' or 't1!=t2', where t1 and
    t2 are terms.

    In either case, we represent the atom as a first-order
    term. Equational literals are represented at terms with faux
    function symbols "=" and "!=".
    """
    atom = parseTerm(lexer)
    if lexer.TestTok([Token.EqualSign, Token.NotEqualSign]):
        # The literal is equational.
        # We get the actual operator, '=' or '!=', followed by the
        # other side of the (in)equation
        op  = lexer.Next().literal
        lhs = atom
        rhs = parseTerm(lexer)
        atom = list([op, lhs, rhs])

    return atom

def atom2String(atom):
    if termFunc(atom) in ["=", "!="]:
        arg1 = termArgs(atom)[0]
        arg2 = termArgs(atom)[1]
        return term2String(arg1)+termFunc(atom)+term2String(arg2)
    else:
        return term2String(atom)


def atomIsConstTrue(atom):
    """
    Return True if the atom is $true.
    """
    return termEqual(atom, ["$true"])


def atomIsConstFalse(atom):
    """
    Return True if the atom is $false.
    """
    return termEqual(atom, ["$false"])


class Literal(object):
    """
    A class representing a literal. A literal is a signed atom. We
    already allow for equational atoms with infix "=" or "!="
    operators, and normalize them on creation.
    """
    def __init__(self, atom, negative=False):
        """
        Initialize a literal. Normalize literals with negative
        equational atoms in the process.
        """

        if termFunc(atom) == "!=":
            self.negative = not negative
            self.atom = list(["="])
            self.atom.extend(termArgs(atom))
        else:
            self.negative = negative
            self.atom = atom
        self.setInferenceLit(True)

    def __repr__(self):
        """
        Return a string representation of the literal.
        """
        if self.isEquational():
            op = "="
            if self.isNegative():
                op = "!="

            result = term2String(termArgs(self.atom)[0])+\
                     op+\
                     term2String(termArgs(self.atom)[1])
        else:
            if self.isNegative():
                result = "~"+term2String(self.atom)
            else:
                result = term2String(self.atom)
        # if(self.isInferenceLit()):
        #    result = result
        return result

    def isEquational(self):
        """
        Return true if the literal is equational.
        """
        return termFunc(self.atom)=="="

    def isPureVarLit(self):
        """
        Return True iff the literal is of the form X=Y
        """
        if self.isEquational():
            return termIsVar(termArgs(self.atom)[0]) and \
                   termIsVar(termArgs(self.atom)[1])
        return False

    def isNegative(self):
        """
        Return true if the literal is negative.
        """
        return self.negative

    def isPositive(self):
        """
        Return true if the literal is positive.
        """
        return not self.negative

    def setInferenceLit(self, inference_lit = True):
        """
        Set the status of the literal as an inference literal. In
        standard biary resolution, all literals are inference
        literals. However, with ordered resolution, literal selection,
        and superposition, only some literals need to be considered
        for generating inferences.
        """
        self.inference_lit = inference_lit

    def isInferenceLit(self):
        """
        Return the status of a literal as inference literal (see
        above).
        """
        return self.inference_lit

    def isPropTrue(self):
        """
        Return True if the literal is of the form $true or ~$false.
        """
        return ((self.isNegative() and
                 atomIsConstFalse(self.atom))
                or
                (self.isPositive() and
                 atomIsConstTrue(self.atom)))

    def isPropFalse(self):
        """
        Return True if the literal is of the form $false or ~$true.
        """
        return ((self.isNegative() and
                 atomIsConstTrue(self.atom))
                or
                (self.isPositive() and
                 atomIsConstFalse(self.atom)))


    def isEqual(self, other):
        """
        Return true if the literal is structurally identical to
        other.
        """
        return self.isNegative()==other.isNegative() and \
               termEqual(self.atom, other.atom)

    def isOpposite(self, other):
        """
        Return true if the atoms of self and other are structurally
        identical to each other, but the sign is the opposite.
        """
        return self.isNegative()!=other.isNegative() and \
               termEqual(self.atom, other.atom)

    def collectVars(self, res=None):
        """
        Insert all variables in self into the set res and return
        it. If res is not given, create it.
        """
        res = termCollectVars(self.atom, res)
        return res

    def collectFuns(self, res=None):
        """
        Insert all function symbols in self into the set res and
        return it. If res is not given, create it.
        """
        res = termCollectFuns(self.atom, res)
        return res

    def collectSig(self, sig=None):
        """
        Collect function- and predicate symbols into the signature. If
        none exists, create it. Return the signature
        """
        if not sig:
            sig = Signature()

        sig.addPred(termFunc(self.atom), len(self.atom)-1)
        for s in termArgs(self.atom):
            termCollectSig(s, sig)
        return sig


    def instantiate(self, subst):
        """
        Return a copy of self, instantiated with the given
        subtitution.
        """
        return Literal(subst(self.atom), self.negative)

    def negate(self):
        """
        Return a copy of self with oposite polarity.
        """
        if self.isPropTrue():
            return Literal(["$false"])
        elif self.isPropFalse():
            return Literal(["$true"])
        else:
            return Literal(termCopy(self.atom), not self.negative)

    def weight(self, fweight, vweight):
        """
        Return the symbol count weight of the literal.
        """
        return termWeight(self.atom, fweight, vweight)

    def match(self, other, subst):
        """
        Try to extend subst a match from self to other. Return True on
        success, False otherwise. In the False case, subst is
        unchanged.
        """
        if self.isNegative()!=other.isNegative():
            return False
        else:
            res =  match(self.atom, other.atom, subst)
            return res

    def predicateAbstraction(self):
        """
        The predicate abstraction of a literal is a pair (pol, pred),
        where pol is an encoding of the polarity (abritrarily True for
        positive, False for negative), and pred is the predicate
        symbol of the atom of the literal. Predicate abstractions can
        be used to quickly reject the possibility that two literals
        can be unified with or matched to each other.
        """
        return (self.isPositive(), termFunc(self.atom))

def parseLiteral(lexer):
    """
    Parse a literal. A literal is an optional negation sign '~',
    followed by an atom.
    """
    negative = False
    if lexer.TestTok(Token.Negation):
        negative = True
        lexer.Next()
    atom = parseAtom(lexer)

    return Literal(atom, negative)


def parseLiteralList(lexer):
    """
    Parse a list of literals separated by "|" (logical or). As per
    TPTP 3 syntax, the single word "$false" is interpreted as the
    false literal, and ignored.
    """
    res = []
    if lexer.LookLit()=="$false":
        lexer.Next()
    else:
        lit = parseLiteral(lexer)
        res.append(lit)

    while lexer.TestTok(Token.Or):
        lexer.Next()

        if lexer.LookLit()=="$false":
            lexer.Next()
        else:
            lit = parseLiteral(lexer)
            res.append(lit)

    return res


def literalList2String(list):
    """
    Convert a literal list to a textual representation that can be
    parsed back.
    """
    if not list:
        return "$false"
    return "|".join(map(repr, list))


def litInLitList(lit, litlist):
    """
    Return true if (a literal equal to) lit is in litlist, false
    otherwise.
    """
    for l in litlist:
        if l.isEqual(lit):
            return True
    return False


def oppositeInLitList(lit, litlist):
    """
    Return true if (a literal equal to) lit is in litlist, false
    otherwise.
    """
    for l in litlist:
        if l.isOpposite(lit):
            return True
    return False


class TestLiterals(unittest.TestCase):
    """
    Unit test class for literals.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.input1="p(X)  ~q(f(X,a), b)  ~a=b  a!=b  ~a!=f(X,b) p(X) ~p(X) p(a)"
        self.input2="p(X)|~q(f(X,a), b)|~a=b|a!=b|~a!=f(X,b)"
        self.input3="$false"
        self.input4="$false|~q(f(X,a), b)|$false"
        self.input5="p(a)|p(f(X))"

        lexer = Lexer(self.input1)
        self.a1 = parseLiteral(lexer)
        self.a2 = parseLiteral(lexer)
        self.a3 = parseLiteral(lexer)
        self.a4 = parseLiteral(lexer)
        self.a5 = parseLiteral(lexer)
        self.a6 = parseLiteral(lexer)
        self.a7 = parseLiteral(lexer)
        self.a8 = parseLiteral(lexer)

    def testLiterals(self):
        """
        Test that basic literal literal functions work
        correctly.
        """

        vars = set()
        print(self.a1)
        self.assertTrue(self.a1.isPositive())
        self.assertTrue(not self.a1.isEquational())
        self.a1.collectVars(vars)
        self.assertEqual(len(vars), 1)
        self.assertEqual(self.a1.collectFuns(), set(["p"]))
        self.assertTrue(self.a1.isInferenceLit())
        self.a1.setInferenceLit(False)
        self.assertTrue(not self.a1.isInferenceLit())

        print(self.a2)
        self.assertTrue(self.a2.isNegative())
        self.assertTrue(not self.a2.isEquational())
        self.a2.collectVars(vars)
        self.assertEqual(len(vars), 1)
        self.assertEqual(self.a2.collectFuns(), set(["q", "f", "a", "b"]))

        print(self.a3)
        self.assertTrue(self.a3.isNegative())
        self.assertTrue(self.a3.isEquational())
        self.assertTrue(self.a3.isEqual(self.a4))
        self.a3.collectVars(vars)
        self.assertEqual(len(vars), 1)

        print(self.a4)
        self.assertTrue(self.a4.isNegative())
        self.assertTrue(self.a4.isEquational())
        self.assertTrue(self.a4.isEqual(self.a3))
        self.a4.collectVars(vars)
        self.assertEqual(len(vars), 1)

        print(self.a5)
        self.assertTrue(not self.a5.isNegative())
        self.assertTrue(self.a5.isEquational())
        self.a5.collectVars(vars)
        self.assertEqual(len(vars), 1)

        print(self.a6, self.a7)
        self.assertTrue(self.a6.isOpposite(self.a7))
        self.assertTrue(self.a7.isOpposite(self.a6))
        self.assertTrue(not self.a6.isOpposite(self.a6))
        self.assertTrue(not self.a6.isOpposite(self.a1))

        self.assertEqual(self.a1.predicateAbstraction(), (True, "p"))
        self.assertEqual(self.a2.predicateAbstraction(), (False, "q"))
        self.assertEqual(self.a3.predicateAbstraction(), (False, "="))



    def testPropProps(self):
        """
        Test if literals are correctly handled as propositional
        constants.
        """
        lex = Lexer("$true $false ~$false ~$true p(a)")
        l1 = parseLiteral(lex)
        l2 = parseLiteral(lex)
        l3 = parseLiteral(lex)
        l4 = parseLiteral(lex)
        l5 = parseLiteral(lex)

        self.assertTrue(l1.isPropTrue())
        self.assertTrue(not l1.isPropFalse())

        self.assertTrue(not l2.isPropTrue())
        self.assertTrue(l2.isPropFalse())

        self.assertTrue(l3.isPropTrue())
        self.assertTrue(not l3.isPropFalse())

        self.assertTrue(not l4.isPropTrue())
        self.assertTrue(l4.isPropFalse())

        self.assertTrue(not l5.isPropTrue())
        self.assertTrue(not l5.isPropFalse())

        l6 = l1.negate()
        self.assertTrue(not l6.isPropTrue())
        self.assertTrue(l6.isPropFalse())

        l7 = l2.negate()
        self.assertTrue(l7.isPropTrue())
        self.assertTrue(not l7.isPropFalse())


    def testAtoms(self):
        """
        Test atom parsing and printing.
        """
        lex = Lexer("p(a) a=b a!=b")
        a = parseAtom(lex)
        print(atom2String(a))
        a = parseAtom(lex)
        print(atom2String(a))
        a = parseAtom(lex)
        print(atom2String(a))

    def testLitWeight(self):
        """
        Test the weight function.
        """
        self.assertEqual(self.a1.weight(2,1),3)
        self.assertEqual(self.a2.weight(2,1),9)
        self.assertEqual(self.a3.weight(2,1),6)
        self.assertEqual(self.a4.weight(2,1),6)
        self.assertEqual(self.a5.weight(2,1),9)

    def testMatch(self):
        """
        Test literal matching.
        """
        self.assertTrue(self.a1.match(self.a1, BTSubst()))
        self.assertTrue(not self.a1.match(self.a2, BTSubst()))

        self.assertTrue(self.a1.match(self.a8, BTSubst()))
        self.assertTrue(not self.a8.match(self.a1, BTSubst()))

        self.assertTrue(not self.a1.match(self.a2, BTSubst()))
        self.assertTrue(not self.a2.match(self.a1, BTSubst()))

    def testLitList(self):
        """
        Test literal list parsing and printing.
        """
        lexer = Lexer(self.input2)
        l2 = parseLiteralList(lexer)
        print(literalList2String(l2))
        self.assertEqual(len(l2),5)

        lexer = Lexer(self.input3)
        l3 = parseLiteralList(lexer)
        print(literalList2String(l3))
        self.assertEqual(len(l3),0)

        lexer = Lexer(self.input4)
        l4 = parseLiteralList(lexer)
        print(literalList2String(l4))
        self.assertEqual(len(l4),1)

        lexer = Lexer(self.input5)
        l5 = parseLiteralList(lexer)
        print(literalList2String(l5))
        self.assertEqual(len(l5),2)

        self.assertTrue(litInLitList(l4[0], l4))
        self.assertTrue(not litInLitList(self.a6, l4))

        self.assertTrue(oppositeInLitList(self.a7, l2))
        self.assertTrue(not oppositeInLitList(self.a7, l4))

    def testSig(self):
        """
        Test signature collection.
        """
        sig = self.a1.collectSig()
        self.a2.collectSig(sig)
        self.a3.collectSig(sig)
        self.a4.collectSig(sig)
        self.a5.collectSig(sig)
        self.a6.collectSig(sig)
        self.a7.collectSig(sig)
        self.a8.collectSig(sig)
        sig.addFun("mult", 2)

        print(sig)
        self.assertTrue(sig.isPred("q"))
        self.assertTrue(not sig.isPred("unknown"))
        self.assertTrue(not sig.isPred("a"))
        self.assertTrue(sig.isFun("a"))
        self.assertTrue(not sig.isFun("unknown"))
        self.assertTrue(not sig.isFun("q"))

        self.assertEqual(sig.getArity("b"),0)
        self.assertEqual(sig.getArity("p"),1)


if __name__ == '__main__':
    unittest.main()
