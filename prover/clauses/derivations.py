"""
A datatype for representing derivations, i.e. jusifications for
clauses and formulas. Derivations are recursively defined: A
derivation can be the trivial derivation (the clause or formula is
read directly from the input), or it consists of an operator (the
inference rule) and a list of parents.

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


class Derivable(object):
    """
    This class represents "derivable" objects. Derivable objects have
    a name and a justification. Names can be generated
    automatically. They are not strictly required to be different for
    different objects, but will usually be (this makes live easier for
    users). Derivable objects will typically be logical formulas,
    either full FOF formulas, or clauses.
    """
    derivedIdCounter = 0
    """
    Counter for generating new clause names.
    """
    printDerivation = False
    """
    Indicate if derivations shouldbe printed as part of Derivable
    objects. It's up to the concrete classes to support this.
    """

    def __init__(self, name=None, derivation=None):
        """
        Initialize the object..
        """
        self.name = None
        self.derivation = derivation
        self.refCount = 0
        self.setName(name)

    def __repr__(self):
        return self.name

    def setName(self, name=None):
        """
        Set the name. If no name is given, generate a default name.
        """
        if name:
            self.name = name
        else:
            self.name = "c%d" % (Derivable.derivedIdCounter,)
            Derivable.derivedIdCounter = Derivable.derivedIdCounter + 1

    def setDerivation(self, derivation):
        self.derivation = derivation

    def getParents(self):
        """
        Return a list of all ancestors of this node in the derivation
        graph.
        """
        if self.derivation:
            return self.derivation.getParents()
        else:
            return []

    def incRefCount(self):
        """
        Increase reference counter (counts virtual edges in the
        derivation graph coming from the children).
        """
        self.refCount = self.refCount + 1

    def decRefCount(self):
        """
        See above.
        """
        self.refCount = self.refCount - 1

    def strDerivation(self):
        """
        If printing of derivations is enabled, return a string
        representartion suitable as part of TPTP-3 output. Otherwise
        return the empty string.
        """
        if not self.derivation:
            return ""
        if Derivable.printDerivation:
            return "," + repr(self.derivation)
        return ""

    def annotateDerivationGraph(self):
        """
        Compute and set the number of virtual edges in all descendents
        of self. The root node has one "virtual" edge.
        """
        if self.refCount == 0:
            parents = self.getParents()
            for p in parents:
                p.annotateDerivationGraph()
        self.incRefCount()

    def linearizeDerivation(self, res=None):
        """
        Return linearized derivation.
        """
        if res is None:
            res = list()
        self.decRefCount()
        if self.refCount == 0:
            res.append(self)
            parents = self.getParents()
            for p in parents:
                p.linearizeDerivation(res)
        return res

    def orderedDerivation(self):
        self.annotateDerivationGraph()
        res = self.linearizeDerivation()
        res.reverse()
        return res


def enableDerivationOutput():
    Derivable.printDerivation = True


def disableDerivationOutput():
    Derivable.printDerivation = False


def toggleDerivationOutput():
    Derivable.printDerivation = not Derivable.printDerivation


class Derivation(object):
    """
    A derivation object. A derivation is either trivial ("input"), a
    reference to an existing Derivable object ("reference"), or an
    inference with a list of premises.
    """

    def __init__(self, operator, parents=None, status="status(thm)"):
        """
        Initialize  a derivation object with the operator and a list
        of parents (which can be Derivations or, in the case of
        "reference", Derivables).
        """
        self.operator = operator
        self.parents = parents
        self.status = status

    def __repr__(self):
        """
        Return a string for the derivation in TPTP-3 format.
        """
        if self.operator == "input":
            return "input"
        elif self.operator == "eq_axiom":
            return "eq_axiom"
        elif self.operator == "reference":
            assert (len(self.parents) == 1)
            return self.parents[0].name
        else:
            return "inference(%s,%s,%s)" % \
                   (self.operator, self.status, repr(self.parents))

    def getParents(self):
        """
        Return a list of all derived objects that are used in this
        derivation.
        """
        if self.operator == "input":
            return []
        elif self.operator == "eq_axiom":
            return []
        elif self.operator == "reference":
            assert (len(self.parents) == 1)
            return self.parents
        else:
            res = []
            for p in self.parents:
                res.extend(p.getParents())
            return res


def flatDerivation(operator, parents, status="status(thm)"):
    """
    Simple convenience function: Create a derivation which directly
    references all parents.
    """
    parentlist = [Derivation("reference", [p]) for p in parents]
    return Derivation(operator, parentlist, status)
