#!/usr/bin/env python3
# ----------------------------------
#
# Module pyres-fof.py

"""
Usage: pyres-fof.py [options] <problem_file>

This is a straightforward implementation of a simple resolution-based
prover for full first-order logic. The problem file should be in
TPTP-3 CNF/FOF syntax. Unsupported features include double quoted
strings/distinct objects. Equality is parsed, and will by default be
dealt with by adding equality axioms for all function- and predicate
symbols.

Options:

 -h
--help
  Print this help.

 -s
--silent
  Supress output of processed given clauses.

 -p
--proof
  Construct and print an explicit proof object (or the derivation of
  the saturated clause set if no proof can be found).

 -i
--index
  Use indexing to speed up some operations.

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

 -n
--neg-lit-selection
  Use the specified negative literal selection function.

 -S
--suppress-eq-axioms
  Do not add equality axioms. This makes the prover incomplete for
  equality problems.

A reasonable command line to run the prover would be:

  ./pyres-fof.py -tifb -HPickGiven5 -nlargest EXAMPLES/PUZ001+1.p

Copyright 2011-2023 Stephan Schulz, schulz@eprover.org

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
import time
from resource import RLIMIT_STACK, setrlimit, getrlimit
import getopt
from signal import signal, SIGXCPU
from resource import getrusage, RUSAGE_SELF
from version import version
from lexer import Token, Lexer
from derivations import (
    enableDerivationOutput,
    disableDerivationOutput,
    Derivable,
    flatDerivation,
)
from clausesets import ClauseSet
from clauses import firstLit, varSizeLit, eqResVarSizeLit
from fofspec import FOFSpec
from heuristics import GivenClauseHeuristics
from saturation import SearchParams, ProofState
from litselection import LiteralSelectors
from alternatingpath_set import SetRelevanceGraph
from alternatingpath_bfs import AdjacencyRelevanceGraph

suppressEqAxioms = False
silent = False
indexed = False
proofObject = False


def processOptions(opts):
    """
    Process the options given
    """
    global silent, indexed, suppressEqAxioms, proofObject

    params = SearchParams()
    for opt, optarg in opts:
        if opt == "-h" or opt == "--help":
            print("pyres-fof.py " + version)
            print(__doc__)
            sys.exit()
        elif opt == "-s" or opt == "--silent":
            silent = True
        elif opt == "-V" or opt == "--version":
            print("% Version: ", version)
        elif opt == "-p" or opt == "--proof":
            proofObject = True
        elif opt == "-i" or opt == "--index":
            indexed = True
        elif opt == "-t" or opt == "--delete-tautologies":
            params.delete_tautologies = True
        elif opt == "-f" or opt == "--forward-subsumption":
            params.forward_subsumption = True
        elif opt == "-b" or opt == "--backward-subsumption":
            params.backward_subsumption = True
        elif opt == "-r" or opt == "--relevance-distance":
            params.relevance_distance = int(optarg)
            params.perform_rel_filter = True
        elif opt == "-g" or opt == "--graph-output-file":
            params.graph_output_file = optarg
        elif opt == "-o" or opt == "--output-rel-neighbourhood":
            params.output_rel_neighbourhood = True
        elif opt == "-H" or opt == "--given-clause-heuristic":
            try:
                params.heuristics = GivenClauseHeuristics[optarg]
            except KeyError:
                print("Unknown clause evaluation function", optarg)
                print("Supported:", GivenClauseHeuristics.keys())
                sys.exit(1)
        elif opt == "-n" or opt == "--neg-lit-selection":
            try:
                params.literal_selection = LiteralSelectors[optarg]
            except KeyError:
                print("Unknown literal selection function", optarg)
                print("Supported:", LiteralSelectors.keys())
                sys.exit(1)
        elif opt == "-S" or opt == "--suppress-eq-axioms":
            suppressEqAxioms = True

    return params


def timeoutHandler(sign, frame):
    """
    This will be called if the process receives a SIGXCPU error. In
    that case, we print an informative message before terminating. We
    expect this signal from the benchmark environment (typically
    StarExec).
    """
    print("% Failure: Resource limit exceeded (time)")
    print("% SZS status ResourceOut")
    sys.exit(0)


def main(from_notebook=False, notebook_opts=[], notebook_args=[]):
    # We try to increase stack space, since we use a lot of
    # recursion. This works differentially well on different OSes, so
    # it is a bit more complex than I would hope for.
    try:
        soft, hard = getrlimit(RLIMIT_STACK)
        soft = 10 * soft
        if hard > 0 and soft > hard:
            soft = hard
        setrlimit(RLIMIT_STACK, (soft, hard))
    except ValueError:
        # For reasons nobody understands, this seems to fail on
        # OS-X. In that case, we just do our best...
        pass

    signal(SIGXCPU, timeoutHandler)
    sys.setrecursionlimit(10000)
    if not from_notebook:
        try:
            opts, args = getopt.gnu_getopt(
                sys.argv[1:],
                "hsVpitfbH:n:Sr:g:o",
                [
                    "help",
                    "silent",
                    "version",
                    "proof",
                    "index",
                    "delete-tautologies",
                    "forward-subsumption",
                    "backward-subsumption",
                    "given-clause-heuristic=",
                    "neg-lit-selection=",
                    "supress-eq-axioms",
                    "relevance-distance=",
                    "graph-output-file=",
                    "output-rel-neighbourhood",
                ],
            )
        except getopt.GetoptError as err:
            print(sys.argv[0], ":", err)
            sys.exit(1)
    params = processOptions(notebook_opts if from_notebook else opts)

    problem = FOFSpec()
    for file in notebook_args if from_notebook else args:
        problem.parse(file)

    if not suppressEqAxioms:
        problem.addEqAxioms()
    cnf = problem.clausify()
    rel_cnf: ClauseSet = ClauseSet()
    if params.perform_rel_filter:
        print(f"# rel_distance: {params.relevance_distance}")
        neg_conjs = cnf.getNegatedConjectures()
        start = time.process_time()
        rel_graph = SetRelevanceGraph(cnf)
        graph_constructed = time.process_time()
        rel_cnf = rel_graph.get_rel_neighbourhood(neg_conjs, params.relevance_distance)
        neighbourhood_computed = time.process_time()
        print(f"# graph_construction_time: {graph_constructed - start}")
        print(
            f"# neighbourhood_computation_time: {neighbourhood_computed - graph_constructed}"
        )
        if params.graph_output_file:
            rel_graph.to_mermaid(params.graph_output_file)
        if params.output_rel_neighbourhood:
            print("% Relevance Neighbourhood:")
            print(rel_cnf)

    state = ProofState(
        params,
        rel_cnf if params.perform_rel_filter else cnf,
        silent,
        indexed,
    )

    res = state.saturate()
    # todo: test alternate path findings properly into statistics and output
    if res != None:
        if problem.isFof and problem.hasConj:
            print("% SZS status Theorem")
        else:
            print("% SZS status Unsatisfiable")
        if proofObject:
            proof = res.orderedDerivation()
            enableDerivationOutput()
            print("% SZS output start CNFRefutation")
            for s in proof:
                print(s)
            print("% SZS output end CNFRefutation")
            disableDerivationOutput()
    else:
        if params.perform_rel_filter and len(rel_cnf) != len(cnf):
            print("%\n% SZS status GaveUp")
        elif problem.isFof and problem.hasConj:
            print("% SZS status CounterSatisfiable")
        else:
            print("% SZS status Satisfiable")
        if proofObject:
            dummy = Derivable(
                "dummy", flatDerivation("pseudoreference", state.processed.clauses)
            )
            sat = dummy.orderedDerivation()
            enableDerivationOutput()
            print("% SZS output start Saturation")
            for s in sat[:-1]:
                print(s)
            print("% SZS output end Saturation")
            disableDerivationOutput()
    print(state.statisticsStr())

    # We use the resources interface to get and print the CPU time
    resources = getrusage(RUSAGE_SELF)
    print("% -------- CPU Time ---------")
    print("%% User time          : %.3f s" % (resources.ru_utime,))
    print("%% System time        : %.3f s" % (resources.ru_stime,))
    print("%% Total time         : %.3f s" % (resources.ru_utime + resources.ru_stime,))


if __name__ == "__main__":
    main()
