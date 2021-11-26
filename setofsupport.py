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



class SOSGenerator(object):
    """ pure virtual class that represents a divison strategy
    of a clauseset into satisfiable set and set-of-support."""
    def markSOS(self, clauseset):
        return


class SOSConjecture(SOSGenerator):
    """ division strategy that adds the negated conjecture into
    the set-of-support and all axioms into the base set.
    This can be done by assuming that the set of all axioms is
    satisfiable and only the negated conjecture makes the set
    unsatisfiable.
    """
    def markSOS(self, clauseset):
        for c in clauseset.clauses:
            if c.type == "negated_conjecture":
                c.part_of_sos = True
            else:
                c.part_of_sos = False

class SOSWhereNegLit(SOSGenerator):
    """ division strategy that adds all clauses with at least one
    negative literal into the set-of-support. This can be done
    because the base set consists of clauses with only positive
    literals which makes the clause set satisfiable by
    interpeting all atoms as true.
    """
    def markSOS(self, clauseset):
        for c in clauseset.clauses:
            c.part_of_sos = False
            for l in c.literals:
                if l.isNegative():
                    c.part_of_sos = True
                    break


class SOSWherePosLit(SOSGenerator):
    """ division strategy that adds all clauses with at least one
    positive literal into the set-of-support. This can be done
    because the base set consists of clauses with only negative
    literals which makes the clause set satisfiable by
    interpreting all atoms as false."""
    def markSOS(self, clauseset):
        for c in clauseset.clauses:
            c.part_of_sos = False
            for l in c.literals:
                if l.isPositive():
                    c.part_of_sos = True
                    break


GivenSOSStrategies = {
    "Conjecture": SOSConjecture(),
    "ContainsNegLit": SOSWhereNegLit(),
    "ContainsPosLit": SOSWherePosLit(),
}