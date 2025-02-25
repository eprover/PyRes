#!/usr/bin/env python3
# ----------------------------------
#
# Module pyres-fof.py
import multiprocessing as mp
import time
import re

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
from PyRes.alternatingpath_set import SetRelevanceGraph
import re

suppressEqAxioms = False
silent = False
indexed = False
proofObject = False


def is_pyres_solvable(problem_path: str):
    file_name = problem_path[problem_path.index("/") + 1 :]
    return bool(re.search("\\+|\\-", file_name))


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


def get_szs_status(problem, params, rel_cnf, cnf, state, res) -> str:
    status = ""
    if res != None:
        if problem.isFof and problem.hasConj:
            status = "SZS status Theorem"
        else:
            status = "SZS status Unsatisfiable"
    else:
        if params.perform_rel_filter and len(rel_cnf) != len(cnf):
            status = "SZS status GaveUp"
        elif problem.isFof and problem.hasConj:
            status = "SZS status CounterSatisfiable"
        else:
            status = "SZS status Satisfiable"
    return status


def try_rel_distance(
    d: int,
    cnf,
    problem,
    params,
    return_dict: dict,
):
    p = mp.current_process()
    return_dict[p.name] = (d, None, None)
    params.relevance_distance = d
    rel_cnf: ClauseSet = ClauseSet()

    if params.perform_rel_filter:
        neg_conjs = cnf.getNegatedConjectures()
        rel_graph = SetRelevanceGraph(cnf)
        rel_cnf = rel_graph.get_rel_neighbourhood(neg_conjs, params.relevance_distance)
    state = ProofState(
        params,
        rel_cnf if params.perform_rel_filter else cnf,
        True,
        indexed,
    )
    res = state.saturate()

    # gave_up = res == None and params.perform_rel_filter and len(rel_cnf) != len(cnf)
    szs_status = get_szs_status(problem, params, rel_cnf, cnf, state, res)
    print((d, True, szs_status))
    return_dict[p.name] = (d, True, szs_status)


def main(from_external=False, external_opts=[], external_args=[]):
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
    if not from_external:
        try:
            opts, args = getopt.gnu_getopt(
                sys.argv[1:],
                "hsVpitfbH:n:Sr:",
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
                ],
            )
        except getopt.GetoptError as err:
            print(sys.argv[0], ":", err)
            sys.exit(1)
    # args = [
    #     file for file in
    #     (external_args if from_external else args)
    #     if is_pyres_solvable(file)
    # ]
    print(
        [
            file
            for file in (external_args if from_external else args)
            if is_pyres_solvable(file)
        ]
    )
    opts = external_args if from_external else opts
    params = processOptions(opts)

    # if(len(args)==0):
    #     print("% SZS status Inappropriate")
    #     return

    problem = FOFSpec()
    for file in args:
        problem.parse(file)

    if not suppressEqAxioms:
        problem.addEqAxioms()
    cnf = problem.clausify()

    params.perform_rel_filter = True
    mp.set_start_method("spawn")
    manager = mp.Manager()
    return_dict = manager.dict()
    tried_rel_distances = []

    SINGLE_RUN_TIMEOUT = 6
    for i in range(1, len(cnf.clauses) + 1):
        p = mp.Process(
            target=try_rel_distance,
            name=f"rel_dist_{i}",
            args=(i, cnf, problem, params, return_dict),
        )
        p.start()
        start = time.time()

        while (time.time() - start <= SINGLE_RUN_TIMEOUT) and p.exitcode is None:
            time.sleep(0.1)
        else:
            p.terminate()
            p.join()

        tried_rel_distances.append(i)
        last_return_state = (
            return_dict.values()[-1][-1] if len(return_dict.values()) > 0 else None
        )
        if last_return_state == "SZS status Unsatisfiable":
            break

    return_list = list(sorted(return_dict.values(), key=lambda item: item[0]))
    print(return_list)

    print(f"% {return_list[-1][-1]}" if len(return_list) > 0 else None)

    # We use the resources interface to get and print the CPU time
    resources = getrusage(RUSAGE_SELF)
    print("% -------- CPU Time ---------")
    print("%% User time          : %.3f s" % (resources.ru_utime,))
    print("%% System time        : %.3f s" % (resources.ru_stime,))
    print("%% Total time         : %.3f s" % (resources.ru_utime + resources.ru_stime,))


if __name__ == "__main__":
    main()
