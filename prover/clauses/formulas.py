"""
A simple implementation of first-order formulas and their associated
meta-information.

See literals.py for the definition of atoms.

A formula is either a first-order-atom, or build from pre-existing
formulas using the various logical connectives and quantifiers:

Assume F,G are arbitrary formulas and X is an arbitrary variable. Then

(~F)
(F&G)
(F|G)
(F->G)
(F<=>G)
(F<~>G)
(F<-G)
(F~&G)
(F~|G)
(![X]:F)
(?[X]:F)

are formulas.

The set of all formulas for a given signature is denoted as
Formulas(P,F,V).

In the external representation, some parentheses can be omitted. Lists
of either conjunctively or disjunctively connected subformula are
assumed to associate left. (F & G & H) is equivalent to ((F&G)&H)

Formulas are represented on two levels: The actual logical formula is
a recursive data structure. This is wrapped in a container that
associates the formula with its meta-information. The implementation
uses literals as the base case, not atoms. That allows us to reuse
some code for parsing and printing infix equality, but also to
represent a formula in Negation Normal Form without any negations in
the frame of the formula.

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

from collections import deque

from prover.clauses.conversion import term2String
from prover.clauses.derivations import Derivable, Derivation, flatDerivation
from prover.clauses.terms import *
from prover.parser.parser import parseTerm, parseLiteral
from prover.parser.token import Token


class Formula(object):
    """
    A class representing a naked first-order formula
    formula. First-order operators are represented as strings, an
    empty operator (i.e. "") indicates an atomic formula.
    child1 and child2 are the subformulas (child2 may be empty).

    In the case of an atomic formula (with operator ""), child1 is
    a Literal object (this unifies parsing and simplifies
    clausification), and child2 is empty (i.e. None).

    In the case of quantified formulae (operator is "!" or "?"),
    child1 is a plain string (i.e. the term representing the variable)
    and child2 is the formula quantified over.

    In the case of a negated formula, the operator is "~", child1 is
    the single subformula, and child2 is empty.

    In the last case (a binary composite formula), the operator is one
    of "&", "|", "=>", "<=", "<=>", "<~>", "~|", "~&", and child1 and
    child2 are the two subformulas.
    """

    def __init__(self, op, child1, child2=None):
        """
        Initialize the formula.
        """
        self.op = op
        self.child1 = child1
        self.child2 = child2

    def __repr__(self):
        """
        Return a string representation of the formula.
        """
        if not self.op:
            res = str(self.child1)
        elif self.op == "~":
            res = "(~" + repr(self.child1) + ")"
        elif self.op in ["&", "|", "=>", "<=", "<=>", "<~>", "~|", "~&"]:
            res = "(" + repr(self.child1) + self.op + repr(self.child2) + ")"
        else:
            assert self.op in ["!", "?"]
            res = "(" + self.op + "[" + term2String(self.child1) + \
                  "]:" + repr(self.child2) + ")"
        return res

    def isLiteral(self):
        """
        Return True if self is a literal.
        """
        return not self.op

    def isPropConst(self, polarity):
        """
        Return True if self is a propositional constant of the given
        polarity.
        """
        if self.isLiteral():
            if polarity:
                return self.child1.isPropTrue()
            else:
                return self.child1.isPropFalse()
        else:
            return False

    def isQuantified(self):
        """
        Return True if self is quantified at the top level.
        """
        return self.op in ["!", "?"]

    def isBinary(self):
        """
        Return True if self has a binary operator at the top level.
        """
        return self.op in ["&", "|", "=>", "<=", "<=>", "<~>", "~|", "~&"]

    def isUnary(self):
        """
        Return True if self has a unary operator at the top level.
        """
        return self.op == "~"

    def isLiteralDisjunction(self):
        """
        Return True iff the formula is a disjunction of literals.
        """
        if self.isLiteral():
            return True
        if self.op == "|":
            return self.child1.isLiteralDisjunction() and \
                   self.child2.isLiteralDisjunction()
        return False

    def isClauseConjunction(self):
        """
        Return True if the formula is a conjunction of disjunction of
        literals.
        """
        if self.isLiteral():
            return True
        if self.op == "|":
            return self.isLiteralDisjunction()
        if self.op == "&":
            return self.child1.isClauseConjunction() and \
                   self.child2.isClauseConjunction()
        return False

    def isCNF(self):
        """
        Return True if the formula is in conjunctive normal form.
        """
        if self.op == "!":
            return self.child2.isCNF()
        return self.isClauseConjunction()

    def getMatrix(self):
        """
        Return the formula without any leading quantifiers (if the
        formula is in prefix normal form, this is the matrix of the
        formuma).
        """
        f = self
        while f.isQuantified():
            f = f.child2
        return f

    def conj2List(self):
        """
        Return a list of the subformula connected by top-level "&".
        """
        if self.op == "&":
            return self.child1.conj2List() + self.child2.conj2List()
        return [self]

    def disj2List(self):
        """
        Return a list of the subformula connected by top-level "|".
        """
        if self.op == "|":
            return self.child1.disj2List() + self.child2.disj2List()
        return [self]

    def hasSubform1(self):
        """
        Return True if self has a proper subformula as the first
        argument. This is false for quantified formulas and literals.
        """
        return self.isUnary() or self.isBinary()

    def hasSubform2(self):
        """
        Return True if self has a proper subformula as the first
        argument. This is the case for quantified formulas and binary
        formulas.
        """
        return self.isQuantified() or self.isBinary()

    def isEqual(self, other):
        """
        Return True if self is structurally equal to other.
        """
        if self.op != other.op:
            return False
        elif self.isLiteral():
            return self.child1.isEqual(other.child1)
        elif self.isQuantified():
            return termEqual(self.child1, other.child1) and \
                   self.child2.isEqual(other.child2)
        elif self.isUnary():
            return self.child1.isEqual(other.child1)
        else:
            return self.child1.isEqual(other.child1) and \
                   self.child2.isEqual(other.child2)

    def collectOps(self):
        """
        Return the set of all (first-order) operators and quantors
        used in the formula. This is mostly for unit-testing
        transformations later on.
        """
        res = {self.op}
        if self.isLiteral():
            pass
        elif self.isUnary():
            res |= self.child1.collectOps()
        elif self.isBinary():
            res |= self.child1.collectOps()
            res |= self.child2.collectOps()
        else:
            assert self.isQuantified()
            res |= self.child2.collectOps()
        return res

    def collectFuns(self):
        """
        Return the set of all function and predicate symbols used in
        the formula.
        """
        res = set()
        if self.isLiteral():
            self.child1.collectFuns(res)
        elif self.isUnary():
            res |= self.child1.collectFuns()
        elif self.isBinary():
            res |= self.child1.collectFuns()
            res |= self.child2.collectFuns()
        else:
            assert self.isQuantified()
            res |= self.child2.collectFuns()
        return res

    def collectSig(self, sig=None):
        """
        Return the set of all function and predicate symbols used in
        the formula.
        """
        if not sig:
            sig = Signature()

        todo = deque()
        todo.append(self)
        while todo:
            f = todo.popleft()
            if f.isLiteral():
                f.child1.collectSig(sig)
            elif f.isUnary():
                todo.append(f.child1)
            elif f.isBinary():
                todo.append(f.child1)
                todo.append(f.child2)
            else:
                assert f.isQuantified()
                todo.append(f.child2)
        return sig

    def collectVars(self):
        """
        Return the set of all variables in self.
        """
        if self.isLiteral():
            res = self.child1.collectVars()
        elif self.isUnary():
            res = self.child1.collectVars()
        elif self.isBinary():
            res = self.child1.collectVars()
            res |= self.child2.collectVars()
        else:
            assert self.isQuantified()
            res = termCollectVars(self.child1)
            res |= self.child2.collectVars()
        return res

    def collectFreeVars(self):
        """
        Return the set of all free variables in self.
        """
        if self.isLiteral():
            res = self.child1.collectVars()
        elif self.isUnary():
            res = self.child1.collectFreeVars()
        elif self.isBinary():
            res = self.child1.collectFreeVars()
            res |= self.child2.collectFreeVars()
        else:
            # Quantor case. We first collect all free variables in
            # the quantified formula, then remove the one bound by the
            # quantifier.
            assert self.isQuantified()
            res = self.child2.collectFreeVars()
            res.discard(self.child1)
        return res


def parseQuantified(lexer, quantor):
    """
    Parse the "remainder" of a formula starting with the given
    quantor.
    """
    lexer.CheckTok(Token.IdentUpper)
    var = parseTerm(lexer)
    if lexer.TestTok(Token.Comma):
        lexer.AcceptTok(Token.Comma)
        rest = parseQuantified(lexer, quantor)
    else:
        lexer.AcceptTok(Token.CloseSquare)
        lexer.AcceptTok(Token.Colon)
        rest = parseUnitaryFormula(lexer)
    res = Formula(quantor, var, rest)
    return res


def parseUnitaryFormula(lexer):
    """
    Parse a "unitary" formula (following TPTP-3 syntax
    terminology). This can be the first unitary formula of a binary
    formula, of course.
    """
    if lexer.TestTok([Token.Universal, Token.Existential]):
        quantor = lexer.LookLit()
        lexer.Next()
        lexer.AcceptTok(Token.OpenSquare)
        res = parseQuantified(lexer, quantor)
    elif lexer.TestTok(Token.OpenPar):
        lexer.AcceptTok(Token.OpenPar)
        res = parseFormula(lexer)
        lexer.AcceptTok(Token.ClosePar)
    elif lexer.TestTok(Token.Negation):
        lexer.AcceptTok(Token.Negation)
        subform = parseUnitaryFormula(lexer)
        res = Formula("~", subform, None)
    else:
        lit = parseLiteral(lexer)
        res = Formula("", lit, None)
    return res


def parseAssocFormula(lexer, head):
    """
    Parse the rest of the associative formula that starts with head
    and continues ([&|] form *).
    """
    op = lexer.LookLit()
    while lexer.TestLit(op):
        lexer.AcceptLit(op)
        next = parseUnitaryFormula(lexer)
        head = Formula(op, head, next)
    return head


def parseFormula(lexer):
    """
    Parse a (naked) formula.
    """
    res = parseUnitaryFormula(lexer)
    if lexer.TestTok([Token.Or, Token.And]):
        res = parseAssocFormula(lexer, res)
    elif lexer.TestTok([Token.Nor, Token.Nand, Token.Equiv,
                        Token.Xor, Token.Implies, Token.BImplies]):
        op = lexer.LookLit()
        lexer.Next()
        rest = parseUnitaryFormula(lexer)
        res = Formula(op, res, rest)
    return res


class WFormula(Derivable):
    """
    Datatype for the complete first-order formula, including
    meta-information like type and name.
    """

    def __init__(self, formula, clause_type="plain", name=None):
        """
        Constructor, takes formula, type, and optional name.
        """
        self.formula = formula
        self.type = clause_type
        Derivable.__init__(self, name)

    def __repr__(self):
        """
        Return a string representation of the formula.
        """
        res = "fof(%s,%s,%s%s)." % (self.name, self.type,
                                    repr(self.formula), self.strDerivation())
        return res

    def collectSig(self, sig=None):
        """
        Collect formula signature.
        """
        return self.formula.collectSig(sig)


def parseWFormula(lexer):
    """
    Parse a formula in (slightly simplified) TPTP-3 syntax. It is
    written
       fof(<name>, <type>, <lformula>).
    where <name> is a lower-case ident, type is a lower-case ident
    from a specific list, and <lformula> is a Formula.

    For us, all clause types are essentially the same, so we only
    distinguish "axiom", "conjecture", and "negated_conjecture", and
    map everything else to "plain".
    """
    lexer.AcceptLit("fof")
    lexer.AcceptTok(Token.OpenPar)
    name = lexer.LookLit()
    lexer.AcceptTok([Token.IdentLower, Token.SQString])
    lexer.AcceptTok(Token.Comma)
    clause_type = lexer.LookLit()
    if clause_type not in ["axiom", "conjecture", "negated_conjecture"]:
        clause_type = "plain"
    lexer.AcceptTok(Token.IdentLower)
    lexer.AcceptTok(Token.Comma)

    form = parseFormula(lexer)

    lexer.AcceptTok(Token.ClosePar)
    lexer.AcceptTok(Token.FullStop)

    res = WFormula(form, clause_type, name)
    res.setDerivation(Derivation("input"))

    return res


def negateConjecture(wform):
    """
    If wform is a conjecture, return its negation. Otherwise
    return it unchanged.
    """

    if wform.type == "conjecture":
        negf = Formula("~", wform.formula)
        negw = WFormula(negf, "negated_conjecture")
        negw.setDerivation(flatDerivation("assume_negation",
                                          [wform],
                                          "status(cth)"))
        return negw
    else:
        return wform
