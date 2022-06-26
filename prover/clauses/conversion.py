from prover.clauses.terms import termIsVar, termArgs, termFunc


def term2String(t):
    """
    Convert a term t into a string.
    """
    if termIsVar(t):
        return t
    else:
        # We need to handle the case of constants separatly
        if not termArgs(t):
            return termFunc(t)
        else:
            arg_rep = ",".join([term2String(s) for s in termArgs(t)])
            return termFunc(t) + "(" + arg_rep + ")"


def atom2String(atom):
    if termFunc(atom) in ["=", "!="]:
        arg1 = termArgs(atom)[0]
        arg2 = termArgs(atom)[1]
        return term2String(arg1) + termFunc(atom) + term2String(arg2)
    else:
        return term2String(atom)


def literalList2String(list):
    """
    Convert a literal list to a textual representation that can be
    parsed back.
    """
    if not list:
        return "$false"
    return "|".join(map(repr, list))