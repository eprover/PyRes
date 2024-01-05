#!/usr/bin/env python3
# ----------------------------------
#
# Module terms.py

"""
A simple implementation of first-order terms. We use nested Python
lists in the style of s-expressions as the term data type.

Definition: Let F be a finite set of function symbols and V be an
enumerable set of variable symbols. Let ar:F->N be the arity function
associating a natural number (the "arity") with each function
symbol. The set of all terms over F and V, Terms(F,V) is defined as
follows:
- For all X in V, X in Term(F,V)
- For all f|n in F and t1,..,tn in Term(F,V), f(t1, ..., tn) in
  Term(F,V).
- Term(F,V) is the smallest set with the above two properties.


In the concrete syntax (i.e. the syntax we use to write terms in ASCII
text form), we represent elements of F by identifers starting with a
lower-case letter. The arity is implicitly given by the number of
argument terms in a term. For function symbols with arity 0, we omit
the parenthesis of the empty argument list.

We represent elements of V by identifiers starting with an upper-case
letter or underscore.

A composite term f(t1, ..., tn) is represented by the list
[f lt1, ..., ltn], where lt1, ..., ltn are lists representing the
subterms. See below for exmples:

"X"          -> "X"
"a"          -> ["a"]
"g(a,b)"     -> ["g", ["a"], ["b"]]
"g(X, f(Y))" -> ["g", "X", ["f", "Y"]]

Note in particular that constant terms are lists with one elements,
not plain strings.

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

import unittest
from lexer import Token,Lexer
from signature import Signature


def termIsVar(t):
    """
    Check if the term is a variable. This assumes that t is a
    well-formed term.
    """
    return type(t)!=type([])


def termIsCompound(t):
    """
    Check if the term is a compound term. This assumes that t is a
    well-formed term.
    """
    return not termIsVar(t)


def termFunc(t):
    """
    Return the function symbol of the compound term t.
    """
    assert termIsCompound(t)
    return t[0]


def termArgs(t):
    """
    Return the argument list of the compound term t.
    """
    assert termIsCompound(t)
    return t[1:]


def term2String(t):
    """
    Convert a term t into a string.
    """
    if termIsVar(t):
        return t
    else:
        # We need to handle the case of constants separatly
        if not termArgs(t):
            return termFunc(t)
        else:
            arg_rep = ",".join([term2String(s) for s in termArgs(t)])
            return termFunc(t)+"("+arg_rep+")"


def parseTermList(lexer):
    """
    Parse a comma-delimited list of terms.
    """
    res = []
    res.append(parseTerm(lexer))
    while lexer.TestTok(Token.Comma):
        lexer.AcceptTok(Token.Comma)
        res.append(parseTerm(lexer))
    return res


def parseTerm(lexer):
    """
    Read a complete term from the lexer provided.
    """
    if lexer.TestTok(Token.IdentUpper):
        res = lexer.Next().literal
    else:
        res = []
        lexer.CheckTok([Token.IdentLower,Token.DefFunctor,Token.SQString])
        res.append(lexer.Next().literal)
        if lexer.TestTok(Token.OpenPar):
            # It's a term with proper subterms, so parse them
            lexer.AcceptTok(Token.OpenPar)
            res.extend(parseTermList(lexer))
            lexer.AcceptTok(Token.ClosePar)
    return res


def string2Term(str):
    """
    Convert a string into a term.
    """
    lexer = Lexer(str)
    return parseTerm(lexer)


def termListEqual(l1, l2):
    """
    Compare two lists of terms.
    """
    if len(l1)!=len(l2):
        return False
    if not l1:
        # l1 is empty, and so, by the previous test, is l2
        return True
    for i in range(len(l1)):
        if not termEqual(l1[i], l2[i]):
            return False
    return True


def termEqual(t1, t2):
    """
    Compare two terms for syntactic equality.
    """
    if termIsVar(t1):
        return t1 == t2
    elif termIsVar(t2):
        return False
    else:
        if termFunc(t1)!=termFunc(t2):
            return False
        return termListEqual(termArgs(t1), termArgs(t2))


def termCopy(t):
    """
    Return a (deep) copy of t. This is the lazy man's way...
    """
    if type(t) == type([]):
        # t is a list, so we copy the elements of the list
        return [termCopy(x) for x in t]
    return t


def termIsGround(t):
    """
    termIsGround(t): Return True if term has no variables, False otherwise
    """
    if termIsVar(t):
        return False
    else:
        for term in termArgs(t):
            if not termIsGround(term):
                return False
        return True


def termCollectVars(t, res=None):
    """
    Insert all variables in t into the set res. For convenience,
    return res. If res is not given, create and return it.
    """
    if res == None:
        res = set()
    if termIsVar(t):
        res.add(t)
    else:
        for s in termArgs(t):
            termCollectVars(s, res)
    return res


def termCollectFuns(t, res=None):
    """
    Insert all function symbols in t into the set res. For
    convenience, return res. If res is not given, create and return
    it.
    """
    if res == None:
        res = set()
    if termIsCompound(t):
        res.add(termFunc(t))
        for s in termArgs(t):
            termCollectFuns(s, res)
    return res


def termCollectSig(t, sig=None):
    """
    Insert all function symbols and their associated arities in t into
    the signature sig. For convenience, return it. If sig is not
    given, create it.
    """
    if sig == None:
        sig = Signature()
    if termIsCompound(t):
        sig.addFun(termFunc(t), len(t)-1)
        for s in termArgs(t):
            termCollectSig(s, sig)
    return sig


def termWeight(t, fweight, vweight):
    """
    Return the weight of the term, counting fweight for each function
    symbol occurance, vweight for each variable occurance.
    Examples:
      termWeight(f(a,b), 1, 1) = 3
      termWeight(f(a,b), 2, 1) = 6
      termWeight(f(X,Y), 2, 1) = 4
      termWeight(X, 2, 1)      = 1
      termWeight(g(a), 3, 1)   = 6
    """
    if termIsVar(t):
        return vweight
    else:
        res = fweight
        for s in termArgs(t):
            res = res + termWeight(s, fweight, vweight)
        return res



def subterm(t, pos):
    """
    Return the subterm of t at position pos (or None if pos is not a
    position in term). pos is a list of integers denoting branches,
    e.g.
       subterm(f(a,b), [])        = f(a,b)
       subterm(f(a,g(b)), [0])    = a
       subterm(f(a,g(b)), [1])    = g(b)
       subterm(f(a,g(b)), [1,0])  = b
       subterm(f(a,g(b)), [3,0])  = None
    """
    if not pos:
        return t
    index = pos.pop(0)
    if index >= len(t):
        return None
    return subterm(t[index],pos)


class TestTerms(unittest.TestCase):
    """
    Test basic term functions.
    """
    def setUp(self):
        self.example1 = "X"
        self.example2 = "a"
        self.example3 = "g(a,b)"
        self.example4 = "g(X, f(Y))"
        self.example5 = "g(X, f(Y))"
        self.example6 = "g(b,b)"
        self.example7 = "'g'(b,b)"
        self.t1 = string2Term(self.example1)
        self.t2 = string2Term(self.example2)
        self.t3 = string2Term(self.example3)
        self.t4 = string2Term(self.example4)
        self.t5 = string2Term(self.example5)
        self.t6 = string2Term(self.example6)
        self.t7 = string2Term(self.example7)


    def testToString(self):
        """
        Test that stringTerm and term2String are dual. Start with
        terms, so that we are sure to get the canonical string
        representation.
        """
        self.assertEqual(string2Term(term2String(self.t1)), self.t1)
        self.assertEqual(string2Term(term2String(self.t2)), self.t2)
        self.assertEqual(string2Term(term2String(self.t3)), self.t3)
        self.assertEqual(string2Term(term2String(self.t4)), self.t4)
        self.assertEqual(string2Term(term2String(self.t7)), self.t7)

    def testIsVar(self):
        """
        Test if the classification function work as expected.
        """
        self.assertTrue(termIsVar(self.t1))
        self.assertTrue(not termIsVar(self.t2))
        self.assertTrue(not termIsVar(self.t3))
        self.assertTrue(not termIsVar(self.t4))


    def testIsCompound(self):
        """
        Test if the classification function work as expected.
        """
        self.assertTrue(not termIsCompound(self.t1))
        self.assertTrue(termIsCompound(self.t2))
        self.assertTrue(termIsCompound(self.t3))
        self.assertTrue(termIsCompound(self.t4))


    def testEquality(self):
        """
        Test if term equality works as expected.
        """
        self.assertTrue(termEqual(self.t1, self.t1))
        self.assertTrue(termEqual(self.t2, self.t2))
        self.assertTrue(termEqual(self.t3, self.t3))
        self.assertTrue(termEqual(self.t4, self.t4))
        self.assertTrue(termEqual(self.t5, self.t5))

        self.assertTrue(termEqual(self.t4, self.t5))

        self.assertTrue(not termEqual(self.t1, self.t4))
        self.assertTrue(not termEqual(self.t3, self.t4))
        self.assertTrue(not termEqual(self.t3, self.t6))

        l1 = []
        l2 = [self.t1]
        self.assertTrue(not termListEqual(l1,l2))


    def testCopy(self):
        """
        Test if term copying works.
        """
        t1 = termCopy(self.t1)
        self.assertTrue(termEqual(t1, self.t1))
        t2 = termCopy(self.t2)
        self.assertTrue(termEqual(t2, self.t2))
        t3 = termCopy(self.t3)
        self.assertTrue(termEqual(t3, self.t3))
        t4 = termCopy(self.t4)
        self.assertTrue(termEqual(t4, self.t4))


    def testIsGround(self):
        """
        Test if isGround() works as expected.
        """
        self.assertTrue(not termIsGround(self.t1))
        self.assertTrue(termIsGround(self.t2))
        self.assertTrue(termIsGround(self.t3))
        self.assertTrue(not termIsGround(self.t4))
        self.assertTrue(not termIsGround(self.t5))

    def testCollectVars(self):
        """
        Test the variable collection.
        """
        vars = termCollectVars(self.t1)
        self.assertEqual(len(vars),1)
        termCollectVars(self.t2, vars)
        self.assertEqual(len(vars),1)
        termCollectVars(self.t3, vars)
        self.assertEqual(len(vars),1)
        termCollectVars(self.t4, vars)
        self.assertEqual(len(vars),2)
        termCollectVars(self.t5, vars)
        self.assertEqual(len(vars),2)

        self.assertTrue("X" in vars)
        self.assertTrue("Y" in vars)


    def testCollectFuns(self):
        """
        Test function symbol collection.
        """
        funs = termCollectFuns(self.t1)
        self.assertEqual(funs, set())

        funs = termCollectFuns(self.t2)
        self.assertEqual(funs, set(["a"]))

        funs = termCollectFuns(self.t3)
        self.assertEqual(funs, set(["g", "a", "b"]))

        funs = termCollectFuns(self.t4)
        self.assertEqual(funs, set(["g", "f"]))

        funs = termCollectFuns(self.t5)
        self.assertEqual(funs, set(["g", "f"]))

        funs = termCollectFuns(self.t6)
        self.assertEqual(funs, set(["g", "b"]))

    def testCollectSig(self):
        """
        Test signature collection.
        """
        sig = termCollectSig(self.t1)
        sig = termCollectSig(self.t2, sig)
        sig = termCollectSig(self.t3, sig)
        sig = termCollectSig(self.t4, sig)
        sig = termCollectSig(self.t5, sig)
        sig = termCollectSig(self.t6, sig)

        self.assertEqual(sig.getArity("f"), 1)
        self.assertEqual(sig.getArity("g"), 2)
        self.assertEqual(sig.getArity("a"), 0)
        self.assertEqual(sig.getArity("b"), 0)


    def testWeight(self):
        """
        Test if termWeight() works as expected.
        """
        self.assertTrue(termWeight(self.t1,1,2) == 2)
        self.assertTrue(termWeight(self.t2,1,2) == 1)
        self.assertTrue(termWeight(self.t3,1,2) == 3)
        self.assertTrue(termWeight(self.t4,1,2) == 6)
        self.assertTrue(termWeight(self.t5,2,1) == 6)

    def testSubterm(self):
        """
        Test if subterm() works as expected.
        self.example5 = "g(X, f(Y))"
        """
        self.assertTrue(subterm(self.t5,[]) == ['g', 'X', ['f', 'Y']])
        self.assertTrue(subterm(self.t5,[0]) == 'g')
        self.assertTrue(subterm(self.t5,[1]) == 'X')
        self.assertTrue(subterm(self.t5,[2,0]) == 'f')
        self.assertTrue(subterm(self.t5,[5,0]) == None)

if __name__ == '__main__':
    unittest.main()
