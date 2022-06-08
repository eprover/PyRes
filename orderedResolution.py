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
from ocb import *


def countsymbols(clauses):
    """
    Count the symbols in all the literals
    Collect signature of symbols
    Return count and signature
    """
    symbol_count = {}
    sig = Signature()
    for clause in clauses.clauses:
        clause.collectSig(sig)
        for lit in clause.literals:
            funs = termCollectFuns(lit.atom)
            for fun in funs:
                old = symbol_count.get(fun)
                if old is None:
                    symbol_count.update({fun: 0})
                    old = symbol_count.get(fun)
                symbol_count.update({fun: old + 1})
    return symbol_count, sig


def initocb(symbolcount, signature, option=1):
    """
    Initialize ocb with sorted counted symbols of all literals and
    weights of var and variable weights of funs
    """
    fun_weight_dict = {}
    fun_prec_dict = {}
    var_weight = 1
    i = 0
    sorted_list = sorted(symbolcount.items(), key=lambda x: x[1], reverse=True)
    # mode selection
    if option == 2:  # fun_weights = 2
        for idx, fun in enumerate(sorted_list):
            fun_weight_dict.update({fun[0]: 2})
            fun_prec_dict.update({fun[0]: idx})
        # var_weight = 1 default

    if option == 3:  # fun_weights = fun_index
        for idx, fun in enumerate(sorted_list):
            fun_weight_dict.update({fun[0]: sorted_list.index(fun)})
            fun_prec_dict.update({fun[0]: idx})
        # var_weight = 1 default

    else:  # default case: all weights 1
        for idx, fun in enumerate(sorted_list):
            fun_weight_dict.update({fun[0]: 1})
            fun_prec_dict.update({fun[0]: idx})
        # var_weight = 1 default

    return OCBCell(fun_weight_dict, var_weight, fun_prec_dict, signature)


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
            elif result == CompareResult.to_equal:
                if a.isNegative():
                    if not b.isNegative():
                        b.setInferenceLit(False)  # a greater b
                elif b.isNegative():
                    a.setInferenceLit(False)  # b greater a
            else:
                assert result == CompareResult.to_uncomparable


if __name__ == '__main__':
    unittest.main()
