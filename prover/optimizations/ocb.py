"""
Implementation of the order control block (ocb)
OCB contains weights for funs (Dict) and weight of variables (unsigned int)
"""

from prover.clauses.terms import *


class OCBCell:

    def __init__(self, ocb_funs=None, var_weight=None):
        if var_weight is None:
            var_weight = {}
        if ocb_funs is None:
            ocb_funs = {}
        self.ocb_funs = ocb_funs
        self.var_weight = var_weight

    """
    For Tests only:
    """

    def insert2dic(self, term, weights=None, var_weight=1):
        if weights is None:
            weights = [1] * len(termCollectFuns(term))
        elif len(termCollectFuns(term)) - len(weights) != 0:
            print("weights and funs don't match")
            assert False
        for idx, fun in enumerate(termCollectFuns(term)):
            self.ocb_funs.update({fun: weights[idx]})
        self.var_weight = var_weight

