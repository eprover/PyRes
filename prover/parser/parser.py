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
from prover.clauses.clause import Clause
from prover.clauses.derivations import Derivation
from prover.clauses.literals import Literal
from prover.parser.lexer import Lexer
from prover.parser.token import Token


def parseTermList(lexer: Lexer):
    """
    Parse a comma-delimited list of terms.
    """
    res = [parseTerm(lexer)]
    while lexer.TestTok(Token.Comma):
        lexer.AcceptTok(Token.Comma)
        res.append(parseTerm(lexer))
    return res


def parseTerm(lexer: Lexer):
    """
    Read a complete term from the lexer provided.
    """
    if lexer.TestTok(Token.IdentUpper):
        res = lexer.Next().literal
    else:
        res = []
        lexer.CheckTok([Token.IdentLower, Token.DefFunctor, Token.SQString])
        res.append(lexer.Next().literal)
        if lexer.TestTok(Token.OpenPar):
            # It's a term with proper subterms, so parse them
            lexer.AcceptTok(Token.OpenPar)
            res.extend(parseTermList(lexer))
            lexer.AcceptTok(Token.ClosePar)
    return res


def parseAtom(lexer: Lexer):
    """
    Parse an atom. An atom is either a conventional atom, in which
    case it's syntactically identical to a term, or it is an
    equational literal, of the form 't1=t2' or 't1!=t2', where t1 and
    t2 are terms.

    In either case, we represent the atom as a first-order
    term. Equational literals are represented at terms with faux
    function symbols "=" and "!=".
    """
    atom = parseTerm(lexer)
    if lexer.TestTok([Token.EqualSign, Token.NotEqualSign]):
        # The literal is equational.
        # We get the actual operator, '=' or '!=', followed by the
        # other side of the (in)equation
        op = lexer.Next().literal
        lhs = atom
        rhs = parseTerm(lexer)
        atom = list([op, lhs, rhs])

    return atom


def parseLiteral(lexer: Lexer):
    """
    Parse a literal. A literal is an optional negation sign '~',
    followed by an atom.
    """
    negative = False
    if lexer.TestTok(Token.Negation):
        negative = True
        lexer.Next()
    atom = parseAtom(lexer)

    return Literal(atom, negative)


def parseLiteralList(lexer: Lexer):
    """
    Parse a list of literals separated by "|" (logical or). As per
    TPTP 3 syntax, the single word "$false" is interpreted as the
    false literal, and ignored.
    """
    res = []
    if lexer.LookLit() == "$false":
        lexer.Next()
    else:
        lit = parseLiteral(lexer)
        res.append(lit)

    while lexer.TestTok(Token.Or):
        lexer.Next()

        if lexer.LookLit() == "$false":
            lexer.Next()
        else:
            lit = parseLiteral(lexer)
            res.append(lit)

    return res


def parseClause(lexer: Lexer):
    """
    Parse a clause. A clause in (slightly simplified) TPTP-3 syntax is
    written as
       cnf(<name>, <type>, <literal list>).
    where <name> is a lower-case ident, type is a lower-case ident
    from a specific list, and <literal list> is a "|" separated list
    of literals, optionally enclosed in parenthesis.

    For us, all clause types are essentially the same, so we only
    distinguish "axiom", "negated_conjecture", and map everything else
    to "plain".
    """
    lexer.AcceptLit("cnf")
    lexer.AcceptTok(Token.OpenPar)
    name = lexer.LookLit()
    lexer.AcceptTok(Token.IdentLower)
    lexer.AcceptTok(Token.Comma)
    clause_type = lexer.LookLit()
    if clause_type not in ["axiom", "negated_conjecture"]:
        clause_type = "plain"
    lexer.AcceptTok(Token.IdentLower)
    lexer.AcceptTok(Token.Comma)
    if lexer.TestTok(Token.OpenPar):
        lexer.AcceptTok(Token.OpenPar)
        lits = parseLiteralList(lexer)
        lexer.AcceptTok(Token.ClosePar)
    else:
        lits = parseLiteralList(lexer)
    lexer.AcceptTok(Token.ClosePar)
    lexer.AcceptTok(Token.FullStop)

    res = Clause(lits, clause_type, name)
    res.setDerivation(Derivation("input"))
    return res