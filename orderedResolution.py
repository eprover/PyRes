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
    varis = set()
    for clause in clauses.clauses:
        for lit in clause.literals:
            funs = termCollectFuns(lit.atom)
            varis = termCollectVars(lit.atom, varis)
            for fun in funs:
                old = symbol_count.get(fun)
                if old is None:
                    symbol_count.update({fun: 0})
                    old = symbol_count.get(fun)
                symbol_count.update({fun: old + 1})
    varis2 = set()
    for v in varis:
        varis2.update(v[:1])
    return symbol_count, varis


def initocb(symbolcount, varis, option=0):
    fun_dict = {}
    var_dict = {}
    sorted_list = sorted(symbolcount.items(), key=lambda x: x[1], reverse=True)
    if option == 0:
        for fun in sorted_list:
            fun_dict.update({fun[0]: 1})
        for var in varis:
            var_dict.update({var: 1})
    print("-----------------------")
    print("INIT_____________OCB")
    print("-----------------------")

    return OCBCell(fun_dict, var_dict)


def selectInferenceLitsOrderedResolution(ocb, given_clause):
    for lit in given_clause.literals:
        if len(given_clause.literals) == 1:
            lit.setInferenceLit(True)
            return
        else:
            lit.setInferenceLit(False)
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
        self.assertEqual(self.given_clause.literals[2].inference_lit, True)
        self.assertEqual(self.given_clause.literals[3].inference_lit, True)


if __name__ == '__main__':
    unittest.main()
