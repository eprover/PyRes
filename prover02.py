#!/usr/bin/env python2.7
# ----------------------------------
#
# Module prover.py

"""
prover02.py 0.1

Usage: prover.py [options] <problem_file>

This is a straightforward implementation of a simple resolution-based
prover for first-order clausal logic. Problem file should be in
(restricted) TPTP-3 CNF syntax. Unsupported features include single-
and double quoted strings and includes. Equality is parsed, but not
interpreted so far.

Options:

 -h
--help
  Print this help.

 -t
--delete-tautologies
  Discard the given clause if it is a tautology.

 -f
--forward-subsumption
  Discard the given clause if it is subsumed by a processed clause.

 -b
--backward-subsumption
  Discard processed clauses if they are subsumed by the given clause.

 -H <heuristic>
--given-clause-heuristic=<heuristic>
  Use the specified heuristic for given-clause selection.

Copyright 2011, 2012 Stephan Schulz, schulz@eprover.org

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
Hirschstrasse 35
76133 Karlsruhe
Germany
Email: schulz@eprover.org
"""

import sys
import getopt
from lexer import Token,Lexer
from derivations import enableDerivationOutput,disableDerivationOutput
from clausesets import ClauseSet
from heuristics import GivenClauseHeuristics
from saturation import SearchParams,ProofState


def processOptions(opts):
    """
    Process the options given
    """
    params = SearchParams()
    for opt, optarg in opts:
        if opt == "-h" or opt == "--help":
            print __doc__
            sys.exit()
        elif opt=="-t" or opt == "--delete-tautologies":
            params.delete_tautologies = True
        elif opt=="-f" or opt == "--forward-subsumption":
            params.forward_subsumption = True
        elif opt=="-b" or opt == "--backward_subsumption":
            params.backward_subsuption = True
        elif opt=="-H" or opr == "--given-clause-heuristic":
            try:
                params.heuristics = GivenClauseHeuristics[optarg]
            except KeyError:
                print "Unknown clause evaluation function", optarg
                sys.exit(1)
                

    return params

if __name__ == '__main__':
    opts, args = getopt.gnu_getopt(sys.argv[1:],
                                   "htfbH:",
                                   ["help",
                                    "delete-tautologies",
                                    "forward-subsumption",
                                    "backward-subsumption"
                                    "given-clause-heuristic="])
    params = processOptions(opts)
    
    problem = ClauseSet()
    for file in args:
        fp = open(file, "r")
        input = fp.read()
        fp.close()
        lex = Lexer(input)
        problem.parse(lex)

    state = ProofState(params, problem)
    res = state.saturate()


    
    print state.statisticsStr()
    if res != None:
        print "# SZS status Unsatisfiable"
        proof = res.orderedDerivation()
        enableDerivationOutput()
        for s in proof:
            print s
        disableDerivationOutput()
    else:
        print "# SZS status Satisfiable"
