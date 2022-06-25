#!/usr/bin/env python3
# ----------------------------------
#
# Module setofsupport.py

"""

Implementation of the set-of-support strategy (SOS)

=== Set-Of-Support ===

The set-of-support strategy is an optional extension of
the basic resolution mechanism. The idea is to divide a whole
unsatisfiable clauseset into two disjoint subsets N and S where
N is a satisfiable clauseset. S is called the set-of-support (SOS).

Because N is satisfiable, any derivations from N will never
result in the empty clause. Therefore at least one clause from the
set-of-support S must be part of every resolution process in order
to derivate the empty clause.

It has been proven (by Lawrence Wos et al. in 1965) that resolution
is still complete if we only allow deductions where at least
one parent clause comes from the set-of-support. This rule decreases
the number of possible derivations and hopefully increases
the overall-performance of the proof.

Example:

We got the following clauseset { A, B, C, D }
Without the set-of-support strategy a new clause may be derived by
every combination of two clauses if resolution is possible.This would
result in a maximum of 6 new clauses because of the 6 combinations
(A,B), (A,C), (A,D), (B,C), (B,D), (C,D).

Now the clauseset is divided into a satisfiable clauseset N
and the set-of-support S.
N = { A, B, D },
S = { C }

The maximum amount of new clauses is now reduced to three
because the combinations (A,B), (A,D) and (B,D) are forbidden.

=== Implementation ===
There are two sos-concepts implemented in PyRes
1) The first concept removes every non-sos-clause from the unprocessed
clauses and adds it to the processed clauses at the beginning of the proof search.
This concept is not compatible with literal selection and ordered resolution

2) The second concept selects sos-clauses and non-sos-clauses in a specific ratio.
This concept is compatible with literal selection and ordered resolution


Copyright 2012-2019 Stephan Schulz, schulz@eprover.org

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
import unittest

from prover.clauses.clausesets import ClauseSet
from prover.optimizations.setofsupport import *
from prover.parser.lexer import Lexer


class TestSos(unittest.TestCase):
    def read_test_problem(self):
        clause_definition = self.spec3 = """
                    cnf(positive_axiom, axiom, p(X)|q(X)).
                    cnf(negative_axiom, axiom, ~p(X)|~q(X)).
                    cnf(mixed_axiom, axiom, ~p(X)| q(X)).
                    cnf(positive_conjecture, negated_conjecture, p(X)|q(X)).
                    cnf(negative_conjecture, negated_conjecture, ~p(X)|~q(X)).
                    cnf(mixed_conjecture, negated_conjecture, ~p(X)| q(X)).
                    """
        lex = Lexer(clause_definition)
        problem = ClauseSet()
        problem.parse(lex)
        return problem

    def test_mark_no_sos(self):
        sos_stategy = GivenSOSStrategies["NoSos"]()
        assert isinstance(sos_stategy, NoSos)
        problem = self.read_test_problem()

        sos_stategy.mark_sos(problem)
        sos_marks = [c.part_of_sos for c in problem.clauses]
        assert sos_marks == [False, False, False, False, False, False]

    def test_mark_sos_conjecture(self):
        sos_stategy = GivenSOSStrategies["Conjecture"]()
        assert isinstance(sos_stategy, SosConjecture)
        problem = self.read_test_problem()

        sos_stategy.mark_sos(problem)
        sos_marks = [c.part_of_sos for c in problem.clauses]
        assert sos_marks == [False, False, False, True, True, True]

    def test_mark_sos_pos_lit(self):
        sos_stategy = GivenSOSStrategies["OnlyPosLit"]()
        assert isinstance(sos_stategy, SosOnlyPosLit)
        problem = self.read_test_problem()

        sos_stategy.mark_sos(problem)
        sos_marks = [c.part_of_sos for c in problem.clauses]
        assert sos_marks == [True, False, False, True, False, False]

    def test_mark_sos_neg_lit(self):
        sos_stategy = GivenSOSStrategies["OnlyNegLit"]()
        assert isinstance(sos_stategy, SosOnlyNegLit)
        problem = self.read_test_problem()

        sos_stategy.mark_sos(problem)
        sos_marks = [c.part_of_sos for c in problem.clauses]
        assert sos_marks == [False, True, False, False, True, False]

    def test_ratio0(self):
        sos_strategy = GivenSOSStrategies["Conjecture"]()
        sos_strategy.ratio = 0

        should_apply_list = [sos_strategy.should_apply() for _ in range(10)]
        assert should_apply_list == [True, True, True, True, True, True, True, True, True, True]

    def test_ratio2(self):
        sos_strategy = GivenSOSStrategies["Conjecture"]()
        sos_strategy.ratio = 2

        should_apply_list = [sos_strategy.should_apply() for _ in range(10)]
        assert should_apply_list == [True, True, False, True, True, False, True, True, False, True]

    def test_ratio_no_sos(self):
        sos_strategy = GivenSOSStrategies["NoSos"]()
        sos_strategy.ratio = 2

        should_apply_list = [sos_strategy.should_apply() for _ in range(10)]
        assert should_apply_list == [False, False, False, False, False, False, False, False, False, False]
