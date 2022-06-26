""" Functions that are not required for PyRes but allow easier testing
are stored in this file.
"""


from prover.parser.lexer import Lexer
from prover.parser.parser import parseTerm


def string2Term(string):
    """
    Convert a string into a term.
    """
    lexer = Lexer(string)
    return parseTerm(lexer)
