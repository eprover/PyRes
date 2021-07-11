#!/usr/bin/env python3
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
from derivations import Derivable,Derivation,flatDerivation,enableDerivationOutput,toggleDerivationOutput
from terms import *
from substitutions import Substitution, freshVar
from literals import Literal
from clauses import Clause
from formulas import Formula, WFormula, parseWFormula, parseFormula


class SkolemSymbols(object):
    """
    Class for providing fresh Skolem symbols.
    """
    skolemCount = 0

    def __init__(self):
        pass

    def newSkolemSymbol(self):
        """
        Return a new skolem symbol. This is a simple version, not
        suitable for a real production system. The symbol is not
        guaranteed to be globally fresh. It's the user's
        responsibility to ensure that no symbols of the form
        "skolemXXXX" are in the input.
        """
        SkolemSymbols.skolemCount += 1
        return "skolem%04d"%(SkolemSymbols.skolemCount,)


    def newSkolemTerm(self, varlist):
        """
        Return a new skolem term for the given (list of) variables.
        """
        symbol = self.newSkolemSymbol()
        res = [symbol]
        res.extend(varlist)
        return res

    def __call__(self, varlist):
        """
        Nicer interface to make getting new Skolem terms more
        convenient.
        """
        return self.newSkolemTerm(varlist)


skolemGenerator = SkolemSymbols()



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
    and m indicates if f'!=f, i.e. if any of the simplification rules
    has been applied.
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
        assert f.op == "" or "Unexpected op"
    return f, False



def formulaSimplify(f):
    """
    Exhaustively apply simplification to f, creating the simplified
    version f'. See formulaTopSimplify()
    above for the individual rules.

    Returns (f', True) if f'!=f, (f', False) otherwise (i.e. if no
    simplification happened because the formula already was completely
    simplified.
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


def formulaVarRename(f, subst = None):
    """
    Rename variables in f so that all bound variables are unique.
    """
    if subst == None:
        subst = Substitution()

    if f.isQuantified():
        # New scope of a variable -> add a new binding to a new
        # variable. Store potential old binding to restore when
        # leaving the scope later
        var = f.child1
        newvar = freshVar()
        oldbinding = subst.modifyBinding((var, newvar))

    if f.isLiteral():
        # Create copy with the new variables recorded in subst
        child = f.child1.instantiate(subst)
        f = Formula("", child)
    else:
        # This is a composite formula. Rename it...
        arg1 = None
        arg2 = None
        if f.isQuantified():
            # Apply new renaming locally to the bound variable and
            # recusively to the subformula
            arg1 = newvar
            arg2 = formulaVarRename(f.child2, subst)
        else:
            # Apply renaming to all subformulas
            if f.hasSubform1():
                arg1 = formulaVarRename(f.child1, subst)
            if f.hasSubform2():
                arg2 = formulaVarRename(f.child2, subst)
        f = Formula(f.op, arg1, arg2)

    if f.isQuantified():
        # We are leaving the scope of the quantifier, so restore
        # substitution.
        subst.modifyBinding((var, oldbinding))

    return f


def formulaRekSkolemize(f, variables, subst):
    """
    Perform Skolemization of f, which is assumed to be in the scope of
    the list of variables provided.
    """
    if f.isLiteral():
        child = f.child1.instantiate(subst)
        f = Formula("", child)
    elif f.op == "?":
        var = f.child1
        skTerm = skolemGenerator(variables)
        oldbinding = subst.modifyBinding((var,skTerm))
        f = formulaRekSkolemize(f.child2, variables, subst)
        subst.modifyBinding((var, oldbinding))
    elif f.op == "!":
        var = f.child1
        variables.append(var)
        handle = formulaRekSkolemize(f.child2, variables, subst)
        f = Formula("!", var, handle)
        variables.pop()
    else:
        arg1 = None
        arg2 = None
        if f.hasSubform1():
            arg1 = formulaRekSkolemize(f.child1, variables, subst)
        if f.hasSubform2():
            arg2 = formulaRekSkolemize(f.child2, variables, subst)
        f = Formula(f.op, arg1, arg2)
    return f



def formulaSkolemize(f):
    """
    Perform an outermost Skolemization of f, removing all existential
    quantifiers. Formulas are considered to be universally closed,
    i.e. free variables (which should not occur) are treated as
    universally quantified.
    """
    vars = f.collectFreeVars()
    varstack = [v for v in vars]

    res = formulaRekSkolemize(f, varstack, Substitution())

    return res


def separateQuantors(f, varlist=None):
    """
    Remove all quantors from f, returning the quantor-free core of the
    formula and a list of quanified variables. This will only be
    applied to Skolemized formulas, thus finding an existential
    quantor is an error. To be useful, the inpt formula also has to be
    variable-normalized.
    """
    if varlist == None:
        varlist = list()

    if f.isQuantified():
        assert f.op == "!"
        varlist.append(f.child1)
        f, dummy = separateQuantors(f.child2, varlist)
    elif f.isLiteral():
        pass
    else:
        arg1 = None
        arg2 = None
        if f.hasSubform1():
            arg1, dummy = separateQuantors(f.child1, varlist)
        if f.hasSubform2():
            arg2, dummy = separateQuantors(f.child2, varlist)
        f = Formula(f.op, arg1, arg2)
    return f, varlist

def formulaShiftQuantorsOut(f):
    """
    Shift all (universal) quantor to the outermost level.
    """
    f, varlist = separateQuantors(f)

    while varlist:
        f = Formula("!", varlist.pop(), f)

    return f


def formulaDistributeDisjunctions(f):
    """
    Convert a Skolemized formula in prefix-NNF form into Conjunctive
    Normal Form.
    """
    arg1 = None
    arg2 = None
    if f.isQuantified():
        arg1 = f.child1
        arg2 = formulaDistributeDisjunctions(f.child2)
        f = Formula(f.op, arg1, arg2)
    elif f.isLiteral():
        pass
    else:
        if f.hasSubform1():
            arg1 = formulaDistributeDisjunctions(f.child1)
        if f.hasSubform2():
            arg2 = formulaDistributeDisjunctions(f.child2)
        f = Formula(f.op, arg1, arg2)
    if f.op == "|":
        if f.child1.op == "&":
            # (P&Q)|R -> (P|R) & (Q|R)
            arg1 = Formula("|", f.child1.child1, f.child2)
            arg2 = Formula("|", f.child1.child2, f.child2)
            f    = Formula("&", arg1, arg2)
            f    = formulaDistributeDisjunctions(f)
        elif  f.child2.op == "&":
            # (R|(P&Q) -> (R|P) & (R|Q)
            arg1 = Formula("|", f.child1, f.child2.child1)
            arg2 = Formula("|", f.child1, f.child2.child2)
            f    = Formula("&", arg1, arg2)
            f    = formulaDistributeDisjunctions(f)
    return f




def formulaCNFSplit(f):
    """
    Given a formula in CNF, convert it to a set of clauses.
    """
    matrix = f.formula.getMatrix()

    res = []
    conjuncts = matrix.conj2List()

    for c in conjuncts:
        litlist = [l.child1 for l in c.disj2List()]
        clause = Clause(litlist, f.type)
        res.append(clause)

    return res



def wFormulaCNF(wf):
    """
    Convert a (wrapped) formula to Conjunctive Normal Form.
    """
    f, m0 = formulaOpSimplify(wf.formula)
    f, m1 = formulaSimplify(f)
    if m0 or m1:
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("fof_simplification", [wf]))
        wf = tmp

    f,m = formulaNNF(f,1)
    if m:
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("fof_nnf", [wf]))
        wf = tmp

    f,m = formulaMiniScope(f)
    if m:
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("shift_quantors", [wf]))
        wf = tmp

    f = formulaVarRename(f)
    if not f.isEqual(wf.formula):
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("variable_rename", [wf]))
        wf = tmp

    f = formulaSkolemize(f)
    if not f.isEqual(wf.formula):
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("skolemize", [wf], "status(esa)"))
        wf = tmp

    f = formulaShiftQuantorsOut(f)
    if not f.isEqual(wf.formula):
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(Derivation("shift_quantors", [wf]))
        wf = tmp

    f = formulaDistributeDisjunctions(f)
    if not f.isEqual(wf.formula):
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("distribute", [wf]))
        wf = tmp

    return wf

def wFormulaClausify(wf):
    """
    Convert a formula into Clause Normal Form.
    """
    wf = wFormulaCNF(wf)

    clauses = formulaCNFSplit(wf)

    for c in clauses:
        c.setDerivation(flatDerivation("split_conjunct", [wf]))

    return clauses




# ------------------------------------------------------------------
#                  Unit test section
# ------------------------------------------------------------------

class TestCNF(unittest.TestCase):
    """
    Test cases for clausification.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
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

        self.testformulas = """
 fof(t12_autgroup,conjecture,(
    ! [A] :
      ( ( ~ v3_struct_0(A)
        & v1_group_1(A)
        & v3_group_1(A)
        & v4_group_1(A)
        & l1_group_1(A) )
     => r1_tarski(k4_autgroup(A),k1_fraenkel(u1_struct_0(A),u1_struct_0(A))) ) )).

fof(abstractness_v1_group_1,axiom,(
    ! [A] :
      ( l1_group_1(A)
     => ( v1_group_1(A)
       => A = g1_group_1(u1_struct_0(A),u1_group_1(A)) ) ) )).

fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) )).
fof(cc1_fraenkel,axiom,(
    ! [A] :
      ( v1_fraenkel(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ( v1_relat_1(B)
            & v1_funct_1(B) ) ) ) )).

fof(cc1_funct_1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) )).

fof(cc1_funct_2,axiom,(
    ! [A,B,C] :
      ( m1_relset_1(C,A,B)
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A,B) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) )).
fof(testscosko, axiom, (![X]:?[Y]:((p(X)&q(X))|q(X,Y))|a)).
        """



    def testOpSimplification(self):
        """
        Test that operator simplification works.
        """
        f,m = formulaOpSimplify(self.f1)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f2)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f3)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f4)
        self.assertTrue(m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

        f,m = formulaOpSimplify(self.f5)
        self.assertTrue(not m)
        self.assertTrue(f.collectOps() <= self.simple_ops)

    def checkSimplificationResult(self, f):
        """
        Simplification results in a formula that does not contain
        the constant predicates $true or $false. The only exception is
        when the whole formula has been has been reduced to a single
        literal (in which case it can be either $true, or $false, or
        any other literal).
        """

        funs = f.collectFuns()
        if f.isPropConst(True) or f.isPropConst(False):
            self.assertTrue(funs in [set(["$true"]), set(["$false"])])
        else:
            self.assertTrue(not "$true" in funs )
            self.assertTrue(not "$false" in funs )


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

        print("NNF:", f)
        if f.isPropConst(True) or f.isPropConst(False):
            funs = f.collectFuns()
            self.assertTrue(funs in [set(["$true"]), set(["$false"])])
        else:
            ops = f.collectOps()
            self.assertTrue(ops <= self.nnf_ops)


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
            print(f, f1, m, expected)
            self.assertEqual(expected, m)
            if m:
                self.assertTrue(not f1.isQuantified())

    def testRenaming(self):
        """
        Test variable renaming
        """
        lex = Lexer("![X]:(p(X)|![X]:(q(X)&?[X]:r(X)))")
        f = parseFormula(lex)

        v1 = f.collectVars()
        self.assertEqual(v1, set(["X"]))
        v2 = f.collectFreeVars()
        self.assertEqual(v2, set())

        f1 = formulaVarRename(f)
        print(f, f1)

        v1 = f1.collectVars()
        self.assertEqual(len(v1), 3)
        v2 = f1.collectFreeVars()
        self.assertEqual(v2, set())

    def testSkolemSymbols(self):
        """
        Check if Skolem symbol construction works.
        """
        symbols = []
        for i in range(10):
            newsymbol = skolemGenerator.newSkolemSymbol()
            self.assertTrue(not newsymbol in symbols)
            symbols.append(newsymbol)

        var = ["X", "Y"]
        for i in range(10):
            t = skolemGenerator(var)
            self.assertTrue(termIsCompound(t))
            self.assertEqual(termArgs(t), var)


    def preprocFormula(self, f):
        """
        Bring formula into miniscoped variable normalized NNF.
        """
        f,m = formulaOpSimplify(f)
        f,m = formulaSimplify(f)
        f,m = formulaNNF(f,1)
        f,m = formulaMiniScope(f)
        f   = formulaVarRename(f)
        return f


    def testSkolemization(self):
        """
        Test skolemization.
        """
        f = self.preprocFormula(self.f2)
        f = formulaSkolemize(f)
        self.assertTrue(not "?" in f.collectOps())
        print(f)

        f = self.preprocFormula(self.f3)
        f = formulaSkolemize(f)
        self.assertTrue(not "?" in f.collectOps())
        print(f)

        f = self.preprocFormula(self.f4)
        f = formulaSkolemize(f)
        self.assertTrue(not "?" in f.collectOps())
        print(f)

    def testShiftQuantors(self):
        """
        Test shifting of quantors out.
        """
        f = self.preprocFormula(self.f2)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        if "!" in f.collectOps():
            self.assertEqual(f.op, "!")

        f = self.preprocFormula(self.f3)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        if "!" in f.collectOps():
            self.assertEqual(f.op, "!")

        f = self.preprocFormula(self.f4)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        if "!" in f.collectOps():
            self.assertEqual(f.op, "!")


    def testDistributeDisjunctions(self):
        """
        Test ConjunctiveNF.
        """
        f = self.preprocFormula(self.f2)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        f = formulaDistributeDisjunctions(f)
        print(f)
        self.assertTrue(f.isCNF())

        f = self.preprocFormula(self.f3)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        f = formulaDistributeDisjunctions(f)
        print(f)
        self.assertTrue(f.isCNF())

        f = self.preprocFormula(self.f4)
        f = formulaSkolemize(f)
        f = formulaShiftQuantorsOut(f)
        f = formulaDistributeDisjunctions(f)
        print(f)
        self.assertTrue(f.isCNF())

    def testCNFization(self):
        """
        Test conversion of wrapped formulas into conjunctive normal
        form.
        """
        lex = Lexer(self.testformulas)

        while not lex.TestTok(Token.EOFToken):
            wf = parseWFormula(lex)
            wf = wFormulaCNF(wf)
            enableDerivationOutput()
            self.assertTrue(wf.formula.isCNF())
            deriv = wf.orderedDerivation()
            print("==================")
            for s in deriv:
                print(s)
            toggleDerivationOutput()

    def testClausification(self):
        """
        Test conversion of wrapped formulas into lists of clauses.
        """
        lex = Lexer(self.testformulas)

        while not lex.TestTok(Token.EOFToken):
            wf = parseWFormula(lex)
            clauses = wFormulaClausify(wf)
            enableDerivationOutput()
            print("==================")
            for c in clauses:
                print(c)
            toggleDerivationOutput()



if __name__ == '__main__':
    unittest.main()
