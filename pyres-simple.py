#!/usr/bin/env python3
# ----------------------------------
#
# Module pyres-simple.py

"""
Usage: pyres-simple.py <problem_file>

This is a straightforward implementation of a simple resolution-based
prover for first-order clausal logic. Problem files should be in
(restricted) TPTP-3 CNF syntax. Unsupported features include double
quoted strings and include file. Equality is parsed, but not
interpreted.

Options:

 -h
--help
  Print this help.

Copyright 2011-2020 Stephan Schulz, schulz@eprover.org

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

import sys
import getopt
from version import version
from lexer import Token,Lexer
from clausesets import ClauseSet
from simplesat import SimpleProofState


def processOptions(opts):
    """
    Process the options given
    """
    for opt, optarg in opts:
        if opt == "-h" or opt == "--help":
            print("pyres-simple.py "+version)
            print(__doc__)
            sys.exit()

if __name__ == '__main__':
    try:
        opts, args = getopt.gnu_getopt(sys.argv[1:],
                                       "h",
                                       ["help"])
    except getopt.GetoptError as err:
        print(sys.argv[0],":", err)
        sys.exit(1)

    processOptions(opts)

    problem = ClauseSet()
    for file in args:
        fp = open(file, "r")
        input = fp.read()
        fp.close()
        lex = Lexer(input)
        problem.parse(lex)

    state = SimpleProofState(problem)
    res = state.saturate()

    if res != None:
        print("# SZS status Unsatisfiable")
    else:
        print("# SZS status Satisfiable")
