"""
A simple lexical analyser that converts a string into a sequence of
tokens.

Copyright 2010-2019 Stephan Schulz, schulz@eprover.org

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program ; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston,
MA  02111-1307 USA

The original copyright holder can be contacted as

Stephan Schulz
Auf der Altenburg 7
70376 Stuttgart
Germany
Email: schulz@eprover.org
"""
from prover.clauses.literals import Literal
from prover.general.idents import Ident


class Token(object):
    """
    Represent a single token with name, position, and print
    representation.
    """
    NoToken = Ident("No Token")
    WhiteSpace = Ident("White Space")
    Comment = Ident("Comment")
    IdentUpper = Ident("Identifier starting with capital letter")
    IdentLower = Ident("Identifier starting with lower case letter")
    DefFunctor = Ident("Defined symbol (starting with a $)")
    Integer = Ident("Positive or negative Integer")
    FullStop = Ident(". (full stop)")
    OpenPar = Ident("(")
    ClosePar = Ident(")")
    OpenSquare = Ident("[")
    CloseSquare = Ident("]")
    Comma = Ident(",")
    Colon = Ident(":")
    EqualSign = Ident("=")
    NotEqualSign = Ident("!=")
    Nand = Ident("~&")
    Nor = Ident("~|")
    Or = Ident("|")
    And = Ident("&")
    Implies = Ident("=>")
    BImplies = Ident("<=")
    Equiv = Ident("<=>")
    Xor = Ident("<~>")
    Universal = Ident("!")
    Existential = Ident("?")
    Negation = Ident("~")
    SQString = Ident("String in 'single quotes'")
    EOFToken = Ident("*EOF*")

    def __init__(self, token_type: Ident, literal: Literal, source: str, pos: int):
        self.type = token_type
        self.literal = literal
        self.source = source
        self.pos = pos

    def __repr__(self):
        return repr((self.type, self.literal))
