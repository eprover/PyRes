"""
This is an implementation of the Knuth Bendix Ordering (KBO)
Based on following definition:

Let >F be a precedence on F, ϕ a weight function admissible
to >F, and s, t ∈ Term(F, V). Then s >kbo t if

    s ≡ f(s1,... , sn), t ≡ g(t1,... , tm), and
        (1) |s|_x ≥ |t|_x for all x ∈ V and
        (2a) ϕ(s) > ϕ(t) or
        (2b) ϕ(s) = ϕ(t), f >F g or
        (2c) ϕ(s) = ϕ(t), f = g, and there is some k with
             s1 ≡ t1,... , s_k−1 ≡ t_k−1, s_k >kbo t_k,
    or s ≡ f(s1,... , sn), t ≡ x ∈ V, and x ∈ Var(s).
"""
import enum

from prover.clauses.terms import *


class CompareResult(enum.Enum):
    to_unknown = 0,
    to_uncomparable = 1,
    to_equal = 2,
    to_greater = 3,
    to_lesser = 4


def kbocomparevars(term_s, term_t):
    """
    variable compare, one term must be a variable, checks for equality and subterms else uncomparable
    retruns CompareResult
    """
    if termIsVar(term_t):
        if term_s == term_t:
            return CompareResult.to_equal
        elif termIsSubterm(term_s, term_t):
            return CompareResult.to_greater
    else:
        assert (termIsVar(term_s))
        if termIsSubterm(term_t, term_s):
            return CompareResult.to_lesser
    return CompareResult.to_uncomparable


def kbocompare(ocb, term_s, term_t):
    """
    KBO Compare implementation
    Compare two terms s,t in the Knuth-Bendix Ordering,
    Return the result
                        to_greater         if s >KBO t
                        to_equal           if s =KBO t
                        to_lesser          if t >KBO s
                        to_uncomparable    otherwise
    """
    if termIsVar(term_s) or termIsVar(term_t):
        return kbocomparevars(term_s, term_t)
    # get termWeight from ocb
    sweight = termocbweight(term_s, ocb)
    tweight = termocbweight(term_t, ocb)
    if sweight > tweight:
        case = kbovarcompare(term_s, term_t)
        if case == CompareResult.to_greater or case == CompareResult.to_equal:
            return CompareResult.to_greater
        elif case == CompareResult.to_lesser or case == CompareResult.to_uncomparable:
            return CompareResult.to_uncomparable
        else:
            assert False
    elif sweight < tweight:
        case = kbovarcompare(term_s, term_t)
        if case == CompareResult.to_lesser or case == CompareResult.to_equal:
            return CompareResult.to_lesser
        elif case == CompareResult.to_greater or case == CompareResult.to_uncomparable:
            return CompareResult.to_uncomparable
        else:
            assert False

    assert (sweight == tweight)  # equal weight
    topsymbolcompare = ocbfuncompare(ocb, termFunc(term_s), termFunc(term_t))  # compare the top symbol of each term
    if topsymbolcompare == CompareResult.to_uncomparable:
        return CompareResult.to_uncomparable
    elif topsymbolcompare == CompareResult.to_greater:
        case = kbovarcompare(term_s, term_t)
        if case == CompareResult.to_greater or case == CompareResult.to_equal:
            return CompareResult.to_greater
        elif case == CompareResult.to_lesser or case == CompareResult.to_uncomparable:
            return CompareResult.to_uncomparable
        else:
            assert False
    elif topsymbolcompare == CompareResult.to_lesser:
        case = kbovarcompare(term_s, term_t)
        if case == CompareResult.to_lesser or case == CompareResult.to_equal:
            return CompareResult.to_lesser
        elif case == CompareResult.to_greater or case == CompareResult.to_uncomparable:
            return CompareResult.to_uncomparable
        else:
            assert False
    elif topsymbolcompare == CompareResult.to_equal:  # same topsymbol, comapre aritys
        sarity = 0
        tarity = 0

        for fun in termCollectFuns(term_s):
            arity = termCollectSig(term_s).getArity(fun)
            if arity > sarity:
                sarity = arity
        for fun in termCollectFuns(term_t):
            arity = termCollectSig(term_t).getArity(fun)
            if arity > tarity:
                tarity = arity
        for i in range(max(sarity, tarity)):
            if tarity <= i:
                case = kbovarcompare(term_s, term_t)
                if case == CompareResult.to_greater or case == CompareResult.to_equal:
                    return CompareResult.to_greater
                elif case == CompareResult.to_lesser or case == CompareResult.to_uncomparable:
                    return CompareResult.to_uncomparable
                else:
                    assert False
            if sarity <= i:
                case = kbovarcompare(term_s, term_t)
                if case == CompareResult.to_lesser or case == CompareResult.to_equal:
                    return CompareResult.to_lesser
                elif case == CompareResult.to_greater or case == CompareResult.to_uncomparable:
                    return CompareResult.to_uncomparable
                else:
                    assert False
            res = kbocompare(ocb, subterm(term_s, [i + 1]), subterm(term_t, [i + 1]))  # args from t and s
            if res == CompareResult.to_greater:
                case = kbovarcompare(term_s, term_t)
                if case == CompareResult.to_greater or case == CompareResult.to_equal:
                    return CompareResult.to_greater
                elif case == CompareResult.to_lesser or case == CompareResult.to_uncomparable:
                    return CompareResult.to_uncomparable
                else:
                    assert False
            elif res == CompareResult.to_lesser:
                case = kbovarcompare(term_s, term_t)
                if case == CompareResult.to_lesser or case == CompareResult.to_equal:
                    return CompareResult.to_lesser
                elif case == CompareResult.to_greater or case == CompareResult.to_uncomparable:
                    return CompareResult.to_uncomparable
                else:
                    assert False
            elif res == CompareResult.to_uncomparable:
                return CompareResult.to_uncomparable
        return CompareResult.to_equal
    else:
        assert False


def kbovarcompare(term_s, term_t):
    """
    Compare the variable occurrences of both terms
    Return CompareResult while adhering to variable condition
    """
    sgreater = False
    tgreater = False
    occurrences_dict = countvaroccurrences(term_t, -1, countvaroccurrences(term_s, 1))
    if any(count > 0 for count in occurrences_dict.values()):
        sgreater = True
    if any(count < 0 for count in occurrences_dict.values()):
        tgreater = True

    if sgreater and tgreater:
        return CompareResult.to_uncomparable
    elif sgreater:
        return CompareResult.to_greater
    elif tgreater:
        return CompareResult.to_lesser
    else:
        return CompareResult.to_equal


def ocbfuncomparepos(ocb, f1, f2):
    """
    Compare positions / precedence of 2 funs in the ocb
    Returns CompareResult
    """
    idx1 = list(ocb.ocb_funs.keys()).index(f1)
    idx2 = list(ocb.ocb_funs.keys()).index(f2)
    res = idx1 - idx2
    if res > 0:
        return CompareResult.to_greater
    elif res < 0:
        return CompareResult.to_lesser
    elif res == 0:
        return CompareResult.to_equal
    else:
        assert False


def ocbfuncompare(ocb, f1, f2):
    """
    Compare 2 funs in the ocb
    $True is the smallest
    Returns CompareResult
    """
    if f1 == f2:
        return CompareResult.to_equal
    if "$True" in f1:
        return CompareResult.to_lesser
    if "$True" in f2:
        return CompareResult.to_greater
    return ocbfuncomparepos(ocb, f1, f2)
