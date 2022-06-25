#!/usr/bin/env python3
# ----------------------------------
#
# Module simplesat.py

"""
Minimalistic implementation of the given-clause algorithm for
saturation of clause sets under the rules of the resolution calculus.

Copyright 2011-2019 Stephan Schulz, schulz@eprover.org

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

from prover.parser.lexer import Lexer
from prover.proof.simplesat import *


class TestSimpleProver(unittest.TestCase):
    """
    Unit test class for simple resolution inference control.
    """
    def setUp(self):
        """
        Setup function for clause/literal unit tests. Initialize
        variables needed throughout the tests.
        """
        print()
        self.spec1 = """
 cnf(axiom, a_is_true, a).
 cnf(negated_conjecture, is_a_true, ~a)."""

        self.spec2 = """
        cnf(axiom, humans_are_mortal, mortal(X)|~human(X)).
        cnf(axiom, socrates_is_human, human(socrates)).
        cnf(negated_conjecture, is_socrates_mortal, ~mortal(socrates)).
"""

        self.spec3 = """
cnf(p_or_q, axiom, p(a)).
cnf(taut, axiom, q(a)).
cnf(not_p, axiom, p(b)).
"""

    def evalSatResult(self, spec, provable):
        """
        Evaluate the result of a saturation compared to the expected
        result.
        """

        lex = Lexer(spec)
        problem = ClauseSet()
        problem.parse(lex)

        prover = SimpleProofState(problem)
        res = prover.saturate()

        if provable:
            self.assertNotEqual(res, None)
            if res == None: # pragma: nocover
                print("# Bug: Should have found a proof!")
            else:
                print("# Proof found")
        else:
            self.assertEqual(res, None)
            if res != None: # pragma: nocover
                print("# Bug: Should not have  found a proof!")
            else:
                print("# No proof found")
                
        
    def testSaturation(self):
        """
        Test that saturation works.
        """
        self.evalSatResult(self.spec1, True)
        self.evalSatResult(self.spec2, True)
        self.evalSatResult(self.spec3, False)

if __name__ == '__main__':
    unittest.main()
