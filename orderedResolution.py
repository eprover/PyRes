#!/usr/bin/env python3
# ----------------------------------
#
# Module orderedResolution.py

"""

"""
from kbo import *
from clauses import *
from literals import *
from ocb import *


def countsymbols(clauses):
    symbol_count = {}
    varis = {}
    for clause in clauses.clauses:
        for lit in clause.literals:
            funs = termCollectFuns(lit.atom)
            varis = termCollectVars(lit.atom)
            for fun in funs:
                old = symbol_count.get(fun)
                if old is None:
                    symbol_count.update({fun: 0})
                    old = symbol_count.get(fun)
                symbol_count.update({fun: old + 1})
    return symbol_count, varis


def initocb(symbolcount, varis, option=0):
    fun_dict = {}
    var_dict = {}
    sorted_list = sorted(symbolcount.items(), key=lambda x: x[1], reverse=True)
    print(sorted_list)
    print(sorted_list[0][0])
    if option == 0:
        for fun in sorted_list:
            fun_dict.update({fun[0]: 1})
        for var in varis:
            var_dict.update({var: 1})
    return OCBCell(fun_dict, var_dict)


def selectInferenceLitsOrderedResolution(ocb, given_clause):
    print(given_clause)
    for lit in given_clause.literals:
        if len(given_clause.literals) == 1:
            lit.setInferenceLit(True)
            return

    for a in given_clause.literals:
        if a.inference_lit is True:
            for b in given_clause.literals:
                if b.inference_lit is True:
                    result = kbocompare(ocb, a.atom, b.atom)
                    if result == CompareResult.to_greater:
                        b.setInferenceLit(False)
                    elif result == CompareResult.to_equal or result == CompareResult.to_uncomparable:
                        pass
                    elif result == CompareResult.to_lesser:
                        a.setInferenceLit(False)
                        break
                    else:
                        assert False


class TestOrderedResolution(unittest.TestCase):
    """
    Test basic  functions.
    """
    def setUp(self):
        self.ocb = None
        self.input1 = "cnf(symmetry,axiom,X15!=X16|X16=X15)."
        lex = Lexer(self.input1)
        self.given_clause = parseClause(lex)
    def testselectInferenceLitsOrderedResolution(self):
        selectInferenceLitsOrderedResolution(self.ocb, self.given_clause)



if __name__ == '__main__':
    unittest.main()
