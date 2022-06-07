#!/usr/bin/env python3
# ----------------------------------
#
# Module orderedResolution.py

"""
Implementation of ordered resolution with KBO
via an order control block


It restricts inferences without sacrificing completeness.
A so-called simplification order is used on the literals
and only resolution steps with (in this order) maximum Literals are allowed.

Ordered Resolution is compatible with negative Literalselection.
Ordered Resolution is then only used if negative Literalselection doesn't select a literal.

Copyright 2010-2021 Stephan Schulz, schulz@eprover.org

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
from kbo import *
from clauses import *
from ocb import *


def countsymbols(clauses):
    """
    Count the symbols in all the literals
    """
    symbol_count = {}
    for clause in clauses.clauses:
        for lit in clause.literals:
            funs = termCollectFuns(lit.atom)
            for fun in funs:
                old = symbol_count.get(fun)
                if old is None:
                    symbol_count.update({fun: 0})
                    old = symbol_count.get(fun)
                symbol_count.update({fun: old + 1})
    return symbol_count


def initocb(symbolcount, option=1):
    """
    Initialize ocb with sorted counted symbols of all literals and
    weights of var and variable weights of funs
    """
    fun_dict = {}
    var_weight = 1
    sorted_list = sorted(symbolcount.items(), key=lambda x: x[1], reverse=True)
    if option == 2:
        for fun in sorted_list:
            fun_dict.update({fun[0]: 2})
        # var_weight = 1 default
    if option == 3:  # weight = index
        for fun in sorted_list:
            fun_dict.update({fun[0]: sorted_list.index(fun)})
        # var_weight = 1 default
    else:   # default case option = 1
        for fun in sorted_list:
            fun_dict.update({fun[0]: 1})
        # var_weight = 1 default

    return OCBCell(fun_dict, var_weight)


def selectInferenceLitsOrderedResolution(ocb, given_clause):
    """
    Select the inferenceLits via kbo
    (Compatible with negLitSelection)
    Maximal Lits are interferenceLits
    """
    for lit in given_clause.literals:
        lit.setInferenceLit(True)
        if len(given_clause.literals) == 1:
            return

    for iter_lit in range(len(given_clause.literals) - 1, 0, -1):
        a = given_clause.literals[iter_lit]
        for iter_lit_2 in range(iter_lit):
            b = given_clause.literals[iter_lit_2]
            result = kbocompare(ocb, a.atom, b.atom)
            if result == CompareResult.to_greater:
                b.setInferenceLit(False)
            elif result == CompareResult.to_lesser:
                a.setInferenceLit(False)
            elif result == CompareResult.to_uncomparable or result == CompareResult.to_equal:
                if a.isNegative():
                    if not b.isNegative():
                        b.setInferenceLit(False)    # a greater b
                elif b.isNegative():
                    a.setInferenceLit(False)        # b greater a
            else:
                assert False


class TestOrderedResolution(unittest.TestCase):
    """
    Test basic functions
    """

    def setUp(self):
        self.input1 = "cnf(c96,plain,butler!=X264|X266!=X265|hates(X264,X265)|~hates(agatha,X266))."
        lex = Lexer(self.input1)
        self.given_clause = parseClause(lex)
        self.ocb = OCBCell()

    def testselectInferenceLitsOrderedResolution(self):
        for lit in self.given_clause.literals:
            self.ocb.insert2dic(lit.atom)
        selectInferenceLitsOrderedResolution(self.ocb, self.given_clause)
        self.assertEqual(self.given_clause.literals[0].inference_lit, False)
        self.assertEqual(self.given_clause.literals[1].inference_lit, True)
        self.assertEqual(self.given_clause.literals[2].inference_lit, False)
        self.assertEqual(self.given_clause.literals[3].inference_lit, True)


if __name__ == '__main__':
    unittest.main()
