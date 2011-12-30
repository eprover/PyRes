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

This basically follows [NW:SmallCNF-2001]. The first version does not
use formula renaming.

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
            return f.child1, True
        elif f.child2.isPropConst(True):
            return f.child2, True
        elif f.child1.isPropConst(False):
            return f.child2, True
        elif f.child2.isPropConst(False):
            return f.child1, True
        elif f.child1.isEqual(f.child2):
            return f.child2, True
    elif f.op == "&":
        if f.child1.isPropConst(True):
            return f.child2, True
        elif f.child2.isPropConst(True):
            return f.child1, True
        elif f.child1.isPropConst(False):
            return f.child1, True
        elif f.child2.isPropConst(False):
            return f.child2, True
        elif f.child1.isEqual(f.child2):
            return f.child2, True
    elif f.op == "<=>":
        if f.child1.isPropConst(True):
            return f.child2, True
        elif f.child2.isPropConst(True):
            return f.child1, True
        elif f.child1.isPropConst(False):
            newform = Formula("~", f.child2)            
            newform, m = formulaSimplify(newform)
            return newform, True
        elif f.child2.isPropConst(False):
            newform = Formula("~", f.child1)            
            newform, m = formulaSimplify(newform)
            return newform, True
        elif f.child1.isEqual(f.child2):
            return Formula("", Literal(["$true"]))
    elif f.op == "=>":
        if f.child1.isPropConst(True):
            return f.child2, True
        elif f.child1.isPropConst(False):
            return Formula("", Literal(["$true"])), True
        elif f.child2.isPropConst(True):
            return Formula("", Literal(["$true"])), True
        elif f.child2.isPropConst(False):
            newform = Formula("~", f.child1)            
            newform, m = formulaSimplify(newform)
            return newform, True
        elif f.child1.isEqual(f.child2):
            return Formula("", Literal(["$true"])), True
    else:
        assert "Unexpected operator "+f.op and False
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

    modified = True

    while modified:
        f, modified = formulaTopSimplify(f)        

    return f, modified

 

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
        ![X]:(a(x) ~| ~a=b)
        ![X]:(a(X)|b(X)|?[X,Y]:(p(X,f(Y))<~>q(g(a),X)))
        ![X]:(a(X) <= ~a=b)
        (((![X]:a(X))|b(X))|(?[X]:(?[Y]:p(X,f(Y)))))~&q(g(a),X)

        """
        lex = Lexer(self.formulas)
        self.f1 = parseFormula(lex)
        self.f2 = parseFormula(lex)
        self.f3 = parseFormula(lex)
        self.f4 = parseFormula(lex)

        self.simple_ops = set(["", "!", "?", "~", "&","|", "=>", "<=>"])
       
    def testOpSimplification(self):
        """
        Test that simplification works.
        """
        f,m = formulaOpSimplify(self.f1)
        self.assert_(f.collectOps() <= self.simple_ops)
        f,m = formulaOpSimplify(self.f2)
        self.assert_(f.collectOps() <= self.simple_ops)
        f,m = formulaOpSimplify(self.f3)
        self.assert_(f.collectOps() <= self.simple_ops)
        f,m = formulaOpSimplify(self.f4)
        self.assert_(f.collectOps() <= self.simple_ops)


        

if __name__ == '__main__':
    unittest.main()
