"""
This module implements heuristic evaluation functions for clauses.
The purpose of heuristic evaluation is selection of clauses during the
resolution process.

A heuristical evaluation function is a function h:Clauses(F,P,X)->R
(where R denotes the set of real numbers, or, in the actual
implementation, the set of floating point numbers).

A lower value of h(C) for some clause C implies that C is assumed to
be better (or more useful) in a given proof search, and should be
processed before a clause C' with larger value h(C').

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


class ClauseEvaluationFunction(object):
    """
    A class representing a clause evaluation function. This is a pure
    virtual class, and it really is just a wrapper around the given
    clause evaluation function. However, some heuristics may need
    to be able to store information, either from initialization, or
    from previous calls.
    """

    def __init__(self):  # pragma: nocover
        """
        Initialize the evaluaton function.
        """
        self.name = "Virtual Base"

    def __repr__(self):  # pragma: nocover
        """
        Return a string representation of the clause evaluation
        function.
        """
        return "ClauseEvalFun(%s)" % (self.name,)

    def __call__(self, clause):
        """
        Provide this as a callable function.
        """
        return self.hEval(clause)

    def hEval(self, clause):  # pragma: nocover
        """
        This needs to be overloaded...
        """
        assert False and "Virtual base class is not callable"


class FIFOEvaluation(ClauseEvaluationFunction):
    """
    Class implementing first-in-first-out evaluation - i.e. clause
    evalutations increase over time (and independent of the clause).
    """

    def __init__(self):
        """
        Initialize object.
        """
        super().__init__()
        self.name = "FIFOEval"
        self.fifocounter = 0

    def hEval(self, clause):
        """
        Actual evaluation function.
        """
        self.fifocounter = self.fifocounter + 1
        return self.fifocounter


class SymbolCountEvaluation(ClauseEvaluationFunction):
    """
    Implement a standard symbol counting heuristic.
    """

    def __init__(self, fweight=2, vweight=1):
        """
        Initialize heuristic.
        """
        super().__init__()
        self.fweight = fweight
        self.vweight = vweight
        self.name = "SymbolCountEval(%f,%f)" % (fweight, vweight)

    def hEval(self, clause):
        """
        Actual evaluation function.
        """
        return clause.weight(self.fweight, self.vweight)


class EvalStructure(object):
    """
    Represent a heuristic clause processing schema. The scheme
    contains several different evaluation functions, and a way to
    alternate between them. Concretely, each evaluation function is
    paired with a counter, and clauses are picked according to each
    function in a weighted round-robin scheme.
    """

    def __init__(self, eval_descriptor):
        """
        Initialize ths structure. The argument is a list of pairs,
        where each pair consists of a function and its relative weight
        count.

        This is internally converted to two arrays:
        eval_funs[] is an array of the different evaluation
                    functions. Each clause receives a a list of
                    evaluations, one from each of the functions in
                    this list.
        eval_vec[]  is the corresponding vector of
                    frequencies. eval_vec[i] indicates, how many
                    clauses should be picked according to eval_fun[i]
                    before switching to the next one, which would be
                    eval_funs[(i+1) % len(eval_funs)].
        The two other members are used to implement this scheme:
        current       is the current evaluation to use.
        current_count indicates, how many more clause will be
                      picked according to current, before current
                      switches to the next value.
        """
        assert len(eval_descriptor)
        self.eval_funs = [pair[0] for pair in eval_descriptor]
        self.eval_vec = [pair[1] for pair in eval_descriptor]
        self.current = 0
        self.current_count = self.eval_vec[0]

    def evaluate(self, clause):
        """
        Return a composite evaluation of a clause.
        """
        evals = [f(clause) for f in self.eval_funs]
        return evals

    def nextEval(self):
        """
        Return the index of the next evaluation function of the
        evaluation scheme.

        Note that we use a while-loop instead of a simple "if" to
        accomodate evaluation functions with a count of 0 (which in
        this way will simply be skipped).
        """
        while not self.current_count:
            self.current = (self.current + 1) % len(self.eval_vec)
            self.current_count = self.eval_vec[self.current]
        self.current_count = self.current_count - 1
        return self.current


FIFOEval = EvalStructure([(FIFOEvaluation(), 1)])
"""
Strict first-in/first out evaluation. This is obviously fair
(i.e. every clause will be picked eventuall), but not a good search
strategy.
"""

SymbolCountEval = EvalStructure([(SymbolCountEvaluation(2, 1), 1)])
"""
Strict symbol counting (a smaller clause is always better than a
larger clause). This is only fair if subsumption or a similar
mechanism is employed, otherwise there can e.g. be an infinite set of
clauses p(X1), p(X2), p(X3),.... that are all smaller than q(f(X)), so
that the latter is never selected.
"""

PickGiven5 = EvalStructure([(SymbolCountEvaluation(2, 1), 5),
                            (FIFOEvaluation(), 1)])
"""
Experiences have shown that picking always the smallest clause (by
symbol count) isn't optimal, but that it pays off to interleave smallest
and oldest clause. The ratio between the two schemes is sometimes
called the "pick-given ratio", and, according to folklore, Larry Wos
has stated that "the optimal pick-given ratio is five." Since he is a
very smart person we use this value here.
"""

PickGiven2 = EvalStructure([(SymbolCountEvaluation(2, 1), 2),
                            (FIFOEvaluation(), 1)])
"""
See above, but now with a pick-given ration of 2 for easier testing.
"""

GivenClauseHeuristics = {
    "FIFO": FIFOEval,
    "SymbolCount": SymbolCountEval,
    "PickGiven5": PickGiven5,
    "PickGiven2": PickGiven2}
"""
Table associating name and evaluation function, so that we can select
the function by name.
"""
