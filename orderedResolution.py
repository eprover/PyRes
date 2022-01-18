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


def initocb(symbolcount, option=0):
    fun_dict = {}
    var_weight = 1
    sorted_list = sorted(symbolcount.items(), key=lambda x: x[1], reverse=True)
    if option == 0:
        for fun in sorted_list:
            fun_dict.update({fun[0]: 1})
        # var_weight = 1 default

    return OCBCell(fun_dict, var_weight)


def selectInferenceLitsOrderedResolution(ocb, given_clause):
    for lit in given_clause.literals:
        lit.setInferenceLit(True)
        if len(given_clause.literals) == 1:
            return
    """
    for a in given_clause.literals:
        for b in given_clause.literals:
            if a != b:
                result = kbocompare(ocb, a.atom, b.atom)
                if result == CompareResult.to_greater:
                    a.setInferenceLit(True)
                    b.setInferenceLit(False)
                elif result == CompareResult.to_lesser:
                    a.setInferenceLit(False)
                    break
                elif result == CompareResult.to_equal or result == CompareResult.to_uncomparable:
                    a.setInferenceLit(True)
                else:
                    assert False
    """

    for iter_lit in range(len(given_clause.literals) - 1, 0, -1):
        a = given_clause.literals[iter_lit]
        for iter_lit_2 in range(iter_lit):
            b = given_clause.literals[iter_lit_2]
            result = kbocompare(ocb, a.atom, b.atom)
            if result == CompareResult.to_greater:
                b.setInferenceLit(False)
            elif result == CompareResult.to_lesser:
                a.setInferenceLit(False)
                #break
            elif result == CompareResult.to_uncomparable or result == CompareResult.to_equal:
                if a.isNegative():
                    if not b.isNegative():
                        b.setInferenceLit(False)    # a greater b
                elif b.isNegative():
                    a.setInferenceLit(False)        # b greater a
                    #break
            else:
                assert False


"""
    candidates = given_clause.literals.copy()
    for a in given_clause.literals:
        if a in candidates:
            for b in given_clause.literals:
                if a != b:
                    result = kbocompare(ocb, a.atom, b.atom)
                    if result == CompareResult.to_greater or result == CompareResult.to_equal:
                        a.setInferenceLit(True)
                        b.setInferenceLit(False)
                        if b in candidates:
                            candidates.remove(b)
                    elif result == CompareResult.to_lesser:
                        a.setInferenceLit(False)
                        if a in candidates:
                            candidates.remove(a)
                        break
                    else:
                        a.setInferenceLit(True)
                        pass
    #for lit in candidates:
       # lit.setInferenceLit(True)
"""


class TestOrderedResolution(unittest.TestCase):
    """
    Test basic  functions.
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
