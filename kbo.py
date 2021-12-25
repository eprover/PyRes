#!/usr/bin/env python3
# ----------------------------------
#
# Module kbo.py

"""

"""
import enum

from terms import *


class CompareResult(enum.Enum):
    to_unknown = 0,
    to_uncomparable = 1,
    to_equal = 2,
    to_greater = 3,
    to_lesser = 4


#def executeKBO(literals):
#    print("KBO")
#    if not literals:
#        return

def kbocomparevars(term_s, term_t):
    if termIsVar(term_t):
        if term_s == term_t:
            return CompareResult.to_equal
        elif termIsSubterm(term_s,term_s):
            return CompareResult.to_greater
    else:
        assert(termIsVar(term_s))
        if termIsSubterm(term_t, term_s):
            return CompareResult.to_lesser
        return CompareResult.to_uncomparable


def kbocompare(term_s, term_t):
    if termIsVar(term_s) or termIsVar(term_t):
        return kbocomparevars(term_s, term_t)
    sweight = termWeight(term_s,1,1) #change numbers
    tweight = termWeight(term_t,1,1) #change numbers

    if sweight > tweight:
        case = kbovarcompare(term_s, term_t)
        if case == (CompareResult.to_greater or CompareResult.to_equal):
            return CompareResult.to_greater
        elif case == (CompareResult.to_lesser or CompareResult.to_uncomparable):
            return CompareResult.to_uncomparable
        else:
            assert False
    elif sweight < tweight:
        case = kbovarcompare(term_s, term_t)
        if case == (CompareResult.to_lesser or CompareResult.to_equal):
            return CompareResult.to_lesser
        elif case == (CompareResult.to_greater or CompareResult.to_uncomparable):
            return CompareResult.to_uncomparable
        else:
            assert False

    assert (sweight == tweight)

    topsymbolcompare= ocbfuncompare(term_s, term_t)  #f-code?
    if topsymbolcompare == CompareResult.to_uncomparable:
        return CompareResult.to_uncomparable
    elif topsymbolcompare == CompareResult.to_greater:
        case = kbovarcompare(term_s, term_t)
        if case == (CompareResult.to_greater or CompareResult.to_equal):
            return CompareResult.to_greater
        elif case == (CompareResult.to_lesser or CompareResult.to_uncomparable):
            return CompareResult.to_uncomparable
        else:
            assert False
    elif topsymbolcompare == CompareResult.to_lesser:
        case = kbovarcompare(term_s, term_t)
        if case == (CompareResult.to_lesser or CompareResult.to_equal):
            return CompareResult.to_lesser
        elif case == (CompareResult.to_greater or CompareResult.to_uncomparable):
            return CompareResult.to_uncomparable
        else:
            assert False
    elif topsymbolcompare == CompareResult.to_equal:
        sarity = termCollectSig(term_s).getArity()
        tarity = termCollectSig(term_t).getArity()
        for i in max(sarity,tarity):
            if tarity <= i:
                case = kbovarcompare(term_s, term_t)
                if case == (CompareResult.to_greater or CompareResult.to_equal):
                    return CompareResult.to_greater
                elif case == (CompareResult.to_lesser or CompareResult.to_uncomparable):
                    return CompareResult.to_uncomparable
                else:
                    assert False
            if sarity <= i:
                case = kbovarcompare(term_s, term_t)
                if case == (CompareResult.to_lesser or CompareResult.to_equal):
                    return CompareResult.to_lesser
                elif case == (CompareResult.to_greater or CompareResult.to_uncomparable):
                    return CompareResult.to_uncomparable
                else:
                    assert False
            res = kbocompare(subterm(term_s, i), subterm(term_t, i))      # args from t and s
            if res == CompareResult.to_greater:
                case = kbovarcompare(term_s, term_t)
                if case == (CompareResult.to_greater or CompareResult.to_equal):
                    return CompareResult.to_greater
                elif case == (CompareResult.to_lesser or CompareResult.to_uncomparable):
                    return CompareResult.to_uncomparable
                else:
                    assert False
            elif res == CompareResult.to_lesser:
                case = kbovarcompare(term_s, term_t)
                if case == (CompareResult.to_lesser or CompareResult.to_equal):
                    return CompareResult.to_lesser
                elif case == (CompareResult.to_greater or CompareResult.to_uncomparable):
                    return CompareResult.to_uncomparable
                else:
                    assert False
            elif res == CompareResult.to_uncomparable:
                return CompareResult.to_uncomparable
        return CompareResult.to_equal
    else:
        assert False




def kbovarcompare(term_s, term_t):  # simplify ?!
    sgreater = False
    tgreater = False

    diff = getvaroccurences(term_s) - getvaroccurences(term_t)
    if diff > 0:
        sgreater = True
    if diff < 0:
        tgreater = True

    if sgreater and tgreater:
        return CompareResult.to_uncomparable
    elif sgreater:
        return CompareResult.to_greater
    elif tgreater:
        return CompareResult.to_lesser
    else:
        return CompareResult.to_equal



