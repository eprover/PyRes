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


def selectInferenceLitsOrderedResolution(given_clause):
    print(given_clause.literals)
    for lit in given_clause.literals:
        if len(given_clause.literals) == 1:
            lit.setInferenceLit(True)
            return
        else:
            lit.setInferenceLit(False)
            print("atom")
            print(lit.atom)

            """
            print("Litlist")
            print(literalList2String(given_clause.literals))
            print("strlit")
            print(term2String(lit))
            print("lit")
            print(lit)
            print("Var?")
            print(termIsVar(lit))
            print("atom")
            print(lit.atom)
            print("weight")
            print(lit.weight(1,2))
            print("funs")
            print(lit.collectFuns())
            print("vars")
            print(lit.collectVars())
            print("Sig")
            print(lit.collectSig())

            input(...)
"""
    ocb = LinkedList(OCBCell("$True", [1]))
    ocb.append(OCBCell("$False", [1]))
    ocb.append(OCBCell("=", [1]))
    for lit in given_clause.literals:
        ocb.append(OCBCell)

    for a in given_clause.literals:
        #if a.isNegative():
            #set1 = a.atom + ["$False"]
        #else:
            #set1 = a.atom + ["$True"]
        for b in given_clause.literals:
            #if b.isNegative():
            #    set2 = b.atom + ["$False"]
            #else:
            #    set2 = b.atom + ["$True"]
            #print(set1)
            #print(set2)
            #input(...)
            result = kbocompare(ocb, a.atom, b.atom)
            if result == CompareResult.to_greater or CompareResult.to_uncomparable:
                a.setInferenceLit(True)
            else:
                print("else")
                a.setInferenceLit(False)
