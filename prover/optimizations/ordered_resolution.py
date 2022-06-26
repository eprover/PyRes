#!/usr/bin/env python3
# ----------------------------------
#
# Module orderedResolution.py

"""

"""
from prover.optimizations.kbo import *
from prover.optimizations.ocb import *


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