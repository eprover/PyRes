#!/usr/bin/env python3
# ----------------------------------
#
# Module setofsupport.py

"""
Copyright 2019 Stephan Schulz, schulz@eprover.org

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
