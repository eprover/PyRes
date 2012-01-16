#!/usr/bin/env python2.7
# ----------------------------------
#
# Module formulacnf.py

"""
Clausification of first-order formulas. Clausification is done in
several steps:

1) Simplification

   Exhaustively apply the simplifiction rules described in the header
   to FormulaSimplify

2) Construction of the Negation Normal Form

3) Miniscoping

4) Variable renaming

5) Skolemization

6) Shift out universal quantors

7) Distribute disjunctions

8) Extract clauses

This basically follows [NW:SmallCNF-2001], albeit with some minor
changes. The first version does not use formula renaming.

@InCollection{NW:SmallCNF-2001,
  author =       {A. Nonnengart and C. Weidenbach},
  title =        {{Computing Small Clause Normal Forms}},
  booktitle =    {Handbook of Automated Reasoning},
  publisher =    {Elsevier Science and MIT Press},
  year =         {2001},
  editor =       {A. Robinson and A. Voronkov},
  volume =       {I},
  chapter =      {5},
  pages =        {335--367}
}


Copyright 2011 Stephan Schulz, schulz@eprover.org

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
Hirschstrasse 35
76133 Karlsruhe
Germany
Email: schulz@eprover.org
"""

import unittest
from lexer import Token,Lexer
from derivations import Derivable,Derivation,toggleDerivationOutput
from terms import *
import substitutions
from literals import Literal
from formulas import Formula, WFormula, parseWFormula, parseFormula


def formulaOpSimplify(f):
    """
    Simplify the formula by eliminating the <=, ~|, ~& and <~>. This
    is not strictly necessary, but means fewer cases to consider
    later. The following rules are applied exhaustively:
    F~|G  -> ~(F|G)
    F~&G  -> ~(F&G)
    F<=G  -> G=>F
    F<~>G -> ~(F<=>G)

    Returns f', modified
    """
    if f.isLiteral():
        return f, False

    modified = False

    # First simplify the subformulas
    if f.hasSubform1():
        child1, m = formulaOpSimplify(f.child1)
        modified |= m
    else:
        child1 = f.child1
    
    if f.hasSubform2():
        child2, m = formulaOpSimplify(f.child2)
        modified |= m
    else:
        child2 = None
        
    if modified:
        f  = Formula(f.op, child1, child2)

    if f.op == "<~>":
        handle = Formula("<=>", f.child1, f.child2)
        newform = Formula("~", handle)
        return newform, True
    elif f.op == "<=":
        newform = Formula("=>", f.child2, f.child1)
        return newform, True
    elif f.op == "~|":
        handle = Formula("|", f.child1, f.child2)
        newform = Formula("~", handle)
        return newform, True
    elif f.op == "~&":
        handle = Formula("&", f.child1, f.child2)
        newform = Formula("~", handle)
        return newform, True
    return f, modified

    

def formulaTopSimplify(f):
    """
    Try to apply the following simplification rules to f at the top
    level. Return (f',m), where f' is the result of simplification,
    and m indicates if f'!=f.
    """
    if f.op == "~":
        if f.child1.isLiteral():
            # Push ~ into literals if possible. This covers the case
            # of ~~P -> P if one of the negations is in the literal.
            return Formula("", f.child1.child1.negate()), True
    elif f.op == "|":
        if f.child1.isPropConst(True):
            # T | P -> T. Note that child1 is $true or
            # equivalent. This applies to several other cases where we
            # can reuse a $true or $false child instead of creating a
            # new formula.
            return f.child1, True
        elif f.child2.isPropConst(True):
            # P | T -> T
            return f.child2, True
        elif f.child1.isPropConst(False):
            # F | P -> P
            return f.child2, True
        elif f.child2.isPropConst(False):
            # P | F -> P
            return f.child1, True
        elif f.child1.isEqual(f.child2):
            # P | P -> P
            return f.child2, True
    elif f.op == "&":
        if f.child1.isPropConst(True):
            # T & P -> P
            return f.child2, True
        elif f.child2.isPropConst(True):
            # P & T -> P
            return f.child1, True
        elif f.child1.isPropConst(False):
            # F & P -> F
            return f.child1, True
        elif f.child2.isPropConst(False):
            # P & F -> F
            return f.child2, True
        elif f.child1.isEqual(f.child2):
            # P & P -> P
            return f.child2, True
    elif f.op == "<=>":
        if f.child1.isPropConst(True):
            # T <=> P -> P
            return f.child2, True
        elif f.child2.isPropConst(True):
            # P <=> T -> P
            return f.child1, True
        elif f.child1.isPropConst(False):
            # P <=> F -> ~P
            newform = Formula("~", f.child2)            
            newform, m = formulaSimplify(newform)
            return newform, True
        elif f.child2.isPropConst(False):
            # F <=> P -> ~P
            newform = Formula("~", f.child1)            
            newform, m = formulaSimplify(newform)
            return newform, True
        elif f.child1.isEqual(f.child2):
            # P <=> P -> T
            return Formula("", Literal(["$true"])), True
    elif f.op == "=>":
        if f.child1.isPropConst(True):
            # T => P -> P
            return f.child2, True
        elif f.child1.isPropConst(False):
            # F => P -> T
            return Formula("", Literal(["$true"])), True
        elif f.child2.isPropConst(True):
            # P => T -> T
            return Formula("", Literal(["$true"])), True
        elif f.child2.isPropConst(False):
            # P => F -> ~P
            newform = Formula("~", f.child1)            
            newform, m = formulaSimplify(newform)
            return newform, True
        elif f.child1.isEqual(f.child2):
            # P => P -> T
            return Formula("", Literal(["$true"])), True
    elif f.op in ["!", "?"]:
        # ![X] F -> F if X is not free in F
        # ?[X] F -> F if X is not free in F
        vars = f.child2.collectFreeVars()        
        if not f.child1 in vars:
            return f.child2, True
    else:
        assert f.op == "" or "Unexpected op"
    return f, False
    
            

def formulaSimplify(f):
    """
    Exhaustively apply simplification to f. See formulaTopSimplify()
    above for the 

    Returns (f', True) if f!=f, (f', False) otherwise. 
    """
    if f.isLiteral():
        return f, False

    modified = False

    # First simplify the subformulas
    if f.hasSubform1():
        child1, m = formulaSimplify(f.child1)
        modified |= m
    else:
        child1 = f.child1
    
    if f.hasSubform2():
        child2, m = formulaSimplify(f.child2)
        modified |= m
    else:
        child2 = None
        
    if modified:
        f  = Formula(f.op, child1, child2)

    topmod = True

    while topmod:
        f, topmod = formulaTopSimplify(f)
        modified |= topmod

    return f, modified


def rootFormulaNNF(f, polarity):
    """
    Apply all NNF transformation rules that can be applied at top
    level. Return result and modification flag.
    """

    normalform = False
    modified   = False

    while not normalform:
        normalform = True
        m = False

        if f.op == "~":
            if f.child1.isLiteral():
                # Move negations into literals
                f = Formula("", f.child1.child1.negate())
                m = True
            elif f.child1.op == "|":
                # De Morgan: ~(P|Q) -> ~P & ~Q
                f = Formula("&",
                            Formula("~", f.child1.child1),
                            Formula("~", f.child1.child2))
                m = True
            elif  f.child1.op == "&":
                # De Morgan: ~(P&Q) -> ~P | ~Q
                f = Formula("|",
                            Formula("~", f.child1.child1),
                            Formula("~", f.child1.child2))
                m = True
            elif f.child1.op == "!":
                # ~(![X]:P) -> ?[X]:~P
                f = Formula("?",
                            f.child1.child1,
                            Formula("~", f.child1.child2))
                m = True
            elif f.child1.op == "?":
                # ~(?[X]:P) -> ![X]:~P
                f = Formula("!",
                            f.child1.child1,
                            Formula("~", f.child1.child2))
                m = True
        elif f.op == "=>":
            # Expand P=>Q into ~P|Q
            f = Formula("|",
                        Formula("~", f.child1),
                        f.child2)
            m = True
        elif f.op == "<=>":
            if polarity == 1:
                # P<=>Q -> (P=>Q)&(Q=>P)
                f = Formula("&",
                            Formula("=>", f.child1, f.child2),
                            Formula("=>", f.child2, f.child1))
                m = True
            else:                
                assert polarity == -1
                # P<=>Q -> (P & Q) | (~P & ~Q)
                f = Formula("|",
                            Formula("&", f.child1, f.child2),
                            Formula("&",
                                    Formula("~", f.child1),
                                    Formula("~", f.child2)))
                m = True
                
        normalform = not m
        modified |= m
    return f, modified


def formulaNNF(f, polarity):
    """
    Convert f into a NNF. Equivalences (<=>) are eliminated
    polarity-dependend, top to bottom. Returns (f', m), where f' is a
    NNF of f, and m indicates if f!=f'
    """

    normalform = False
    modified   = False

    while not normalform:
        normalform = True
        f, m = rootFormulaNNF(f, polarity)
        modified |= m
        
        if f.op == "~":
            handle, m = formulaNNF(f.child1, -polarity)
            if m:
                normalform = False
                f = Formula("~", handle)
        elif f.op in ["!", "?"]:
            handle, m = formulaNNF(f.child2, polarity)
            if m:
                normalform = False
                f = Formula(f.op, f.child1, handle)
        elif f.op in ["|", "&"]:
            handle1, m1 = formulaNNF(f.child1, polarity)
            handle2, m2 = formulaNNF(f.child2, polarity)
            m = m1 or m2
            if m:
                normalform = False
                f = Formula(f.op, handle1, handle2)
        else:
            assert f.isLiteral()
        modified |= m

    return f, modified

def formulaMiniScope(f):
    """
    Perform miniscoping, i.e. move quantors in as far as possible, so
    that their scope is only the smallest subformula in which the
    variable occurs. 
    """
    res = False
    if f.isQuantified():
        op    = f.child2.op
        quant = f.op
        var   = f.child1        
        subf  = f.child2
        if op == "&" or op == "|":
            if not var in subf.child1.collectFreeVars():
                # q[X]:(P op Q)  -> P op (q[X]:Q) if X not free in P
                arg2 = Formula(quant, var, subf.child2)
                arg1 = subf.child1
                f = Formula(op, arg1, arg2)
                res = True
            elif not var in subf.child2.collectFreeVars():
                # q[X]:(P op Q)  -> (q[X]:P) op Q if X not free in Q
                arg1 = Formula(quant, var, subf.child1)
                arg2 = subf.child2
                f = Formula(op, arg1, arg2)
                res = True
            else:
                if op == "&" and quant == "!":
                    # ![X]:(P&Q) -> ![X]:P & ![X]:Q
                    arg1 = Formula("!", var, subf.child1)
                    arg2 = Formula("!", var, subf.child2)
                    f = Formula("&" , arg1, arg2)
                    res = True
                elif  op == "|" and quant == "?":
                    # ?[X]:(P|Q) -> ?[X]:P | ?[X]:Q
                    arg1 = Formula("?", var, subf.child1)
                    arg2 = Formula("?", var, subf.child2)
                    f = Formula("|", arg1, arg2)
                    res = True
    arg1 = f.child1
    arg2 = f.child2
    modified = False
    if f.hasSubform1():
        arg1, m = formulaMiniScope(f.child1)
        modified |= m
    if f.hasSubform2():
        arg2, m = formulaMiniScope(f.child2)
        modified |= m
    if modified:
        f = Formula(f.op, arg1, arg2)
        f,m = formulaMiniScope(f)
        res = True
    return f, res



class TestCNF(unittest.TestCase):
    """
    Test cases for clausification.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print
        self.formulas = """
        ![X]:(a(X) ~| ~a=b)
        ![X]:(a(X)|b(X)|?[X,Y]:(p(X,f(Y))<~>q(g(a),X)))
        ![X]:(a(X) <= ~a=b)
        ((((![X]:a(X))|b(X))|(?[X]:(?[Y]:p(X,f(Y)))))~&q(g(a),X))
        ![X]:(a(X)|$true)        
        """
        lex = Lexer(self.formulas)
        self.f1 = parseFormula(lex)
        self.f2 = parseFormula(lex)
        self.f3 = parseFormula(lex)
        self.f4 = parseFormula(lex)
        self.f5 = parseFormula(lex)
        self.simple_ops = set(["", "!", "?", "~", "&","|", "=>", "<=>"])
        self.nnf_ops = set(["", "!", "?", "&","|"])

        self.covformulas ="""
        (a|$true)
        ($true|a)
        (a|$false)
        ($false|a)
        (a|a)
        (a&$true)
        ($true&a)
        (a&$false)
        ($false&a)
        (a&a)
        (a=>$true)
        ($true=>a)
        (a=>$false)
        ($false=>a)
        (a=>a)
        (a<=>$true)
        ($true<=>a)
        (a<=>$false)
        ($false<=>a)
        (a<=>a)
        ![X]:(a<=>a)
        ?[X]:(a<=>a)
        a<=>b
        """

        
       
    def testOpSimplification(self):
        """
        Test that operator simplification works.
        """
        f,m = formulaOpSimplify(self.f1)
        self.assert_(m)
        self.assert_(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f2)
        self.assert_(m)
        self.assert_(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f3)
        self.assert_(m)
        self.assert_(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f4)
        self.assert_(m)
        self.assert_(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f5)
        self.assert_(not m)
        self.assert_(f.collectOps() <= self.simple_ops)

    def checkSimplificationResult(self, f):
        """
        A simplified formula has no $true/$false, or it is a literal
        (in which case it's either true or false).
        """

        funs = f.collectFuns()
        if f.isPropConst(True) or f.isPropConst(False):
            self.assert_(funs in [set(["$true"]), set(["$false"])])
        else:
            self.assert_(not "$true" in funs )
            self.assert_(not "$false" in funs )
        

    def testSimplification(self):
        """
        Test that simplification works.
        """
        f,m = formulaOpSimplify(self.f1)
        f,m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f,m = formulaOpSimplify(self.f2)
        f,m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f,m = formulaOpSimplify(self.f3)
        f,m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f,m = formulaOpSimplify(self.f4)
        f,m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        f,m = formulaOpSimplify(self.f5)
        f,m = formulaSimplify(f)
        self.checkSimplificationResult(f)

        lex = Lexer(self.covformulas)
        while not lex.TestTok(Token.EOFToken):
            f = parseFormula(lex)
            f,m = formulaOpSimplify(f)
            f,m = formulaSimplify(f)
            self.checkSimplificationResult(f)

    
    def checkNNFResult(self, f):
        """
        A simplified formula is either $true/$false, or it only
        contains &, |, !, ? as operators (~ is shifted into the
        literals).
        """

        print "NNF:", f
        if f.isPropConst(True) or f.isPropConst(False):
            funs = f.collectFuns()
            self.assert_(funs in [set(["$true"]), set(["$false"])])
        else:
            ops = f.collectOps()
            self.assert_(ops <= self.nnf_ops)
            

    def testNNF(self):
        """
        Test NNF transformation
        """
        f,m = formulaOpSimplify(self.f1)
        f,m = formulaSimplify(f)
        f,m = formulaNNF(f, 1)
        self.checkNNFResult(f)

        f,m = formulaOpSimplify(self.f2)
        f,m = formulaSimplify(f)
        f,m = formulaNNF(f,1)
        self.checkNNFResult(f)

        f,m = formulaOpSimplify(self.f3)
        f,m = formulaSimplify(f)
        f,m = formulaNNF(f,1)
        self.checkNNFResult(f)

        f,m = formulaOpSimplify(self.f4)
        f,m = formulaSimplify(f)
        f,m = formulaNNF(f,1)
        self.checkNNFResult(f)

        f,m = formulaOpSimplify(self.f5)
        f,m = formulaSimplify(f)
        f,m = formulaNNF(f,1)
        self.checkNNFResult(f)

        lex = Lexer(self.covformulas)
        while not lex.TestTok(Token.EOFToken):
            f = parseFormula(lex)
            f,m = formulaOpSimplify(f)
            f,m = formulaSimplify(f)
            f,m = formulaNNF(f,1)
            self.checkNNFResult(f)

    def testMiniScope(self):
        """
        Test Miniscoping.
        """
        lex = Lexer("""
        ![X]:(p(X)|q(a))
        ?[X]:(p(a)&q(X))
        ![X]:(p(X)&q(X))
        ?[X]:(p(X)|q(X))
        ![X]:(p(X)|q(X))
        ![X,Y]:?[Z]:(p(Z)|q(X))
        """)
        res = [True, True, True, True, False, True]

        while not lex.TestTok(Token.EOFToken):
            expected = res.pop(0)
            f = parseFormula(lex)
            f1,m = formulaMiniScope(f)
            print f, f1, m, expected
            self.assertEqual(expected, m)
            if m:
                self.assert_(not f1.isQuantified())
            

if __name__ == '__main__':
    unittest.main()
