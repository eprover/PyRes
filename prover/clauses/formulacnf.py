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

from prover.clauses.clauses import Clause
from prover.clauses.derivations import Derivation, flatDerivation
from prover.clauses.formulas import Formula, WFormula
from prover.clauses.literals import Literal
from prover.proof.substitutions import Substitution, freshVar


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
        return "skolem%04d" % (SkolemSymbols.skolemCount,)

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
        f = Formula(f.op, child1, child2)

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
        if f.child1 not in vars:
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
        f = Formula(f.op, child1, child2)

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
    modified = False

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
            elif f.child1.op == "&":
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
    modified = False

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
        op = f.child2.op
        quant = f.op
        var = f.child1
        subf = f.child2
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
                    f = Formula("&", arg1, arg2)
                    res = True
                elif op == "|" and quant == "?":
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
        f, m = formulaMiniScope(f)
        res = True
    return f, res


def formulaVarRename(f, subst=None):
    """
    Rename variables in f so that all bound variables are unique.
    """
    if subst is None:
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
        oldbinding = subst.modifyBinding((var, skTerm))
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
            f = Formula("&", arg1, arg2)
            f = formulaDistributeDisjunctions(f)
        elif f.child2.op == "&":
            # (R|(P&Q) -> (R|P) & (R|Q)
            arg1 = Formula("|", f.child1, f.child2.child1)
            arg2 = Formula("|", f.child1, f.child2.child2)
            f = Formula("&", arg1, arg2)
            f = formulaDistributeDisjunctions(f)
    return f


def formulaCNFSplit(f):
    """
    Given a formula in CNF, convert it to a set of clauses.
    """
    matrix = f.formula.getMatrix()

    res = []
    conjuncts = matrix.conj2List()

    for c in conjuncts:
        litlist = [lit.child1 for lit in c.disj2List()]
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

    f, m = formulaNNF(f, 1)
    if m:
        tmp = WFormula(f, wf.type)
        tmp.setDerivation(flatDerivation("fof_nnf", [wf]))
        wf = tmp

    f, m = formulaMiniScope(f)
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
