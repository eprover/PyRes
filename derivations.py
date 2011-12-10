#!/usr/bin/env python2.7
# ----------------------------------
#
# Module derivations.py

"""
A datatype for representing derivations, i.e. jusifications for
clauses and formulas. Derivations are recursively defined: A
derivation can be the trivial derivation (the clause or formula is
read directly from the input), or it consists of an operator (the
inference rule) and a list of parents.

Copyright 2011 Stephan Schulz, schulz@eprover.org

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

import unittest


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
    def __init__(self, name=None, derivation = None):
        """
        Initialize the object..
        """
        self.setName(name)
        self.derivation = derivation
        self.childrenCount = 0

    def __repr__(self):
        return self.name

    def setName(self, name = None):
        """
        Set the name. If no name is given, generate a default name.
        """
        if name:
            self.name = name
        else:
            self.name = "c%d"%(Derivable.derivedIdCounter,)
            Derivable.derivedIdCounter=Derivable.derivedIdCounter+1        

    def setDerivation(self, derivation):
        self.derivation = derivation

    def getParents(self):
        if self.derivation:
            return self.derivation.getParents()
        else:
            return []

    def incChildCount(self):
        self.childrenCount = self.childrenCount+1
        
    def decChildCount(self):
        self.childrenCount = self.childrenCount-1


class Derivation(object):
    """
    A derivation object. A derivation is either trivial ("input"), a
    reference to an existing Derivable object ("reference"), or an
    inference with a list of premises. 
    """
    def __init__(self, operator, parents=None):
        """
        """
        self.operator = operator
        self.parents  = parents
 
    def __repr__(self):
        if self.operator == "input":
            return "input"
        elif self.operator == "binres":
            return "inference(resolution, [status(thm)], "\
                   +repr(self.parents)+")"    
        elif self.operator == "factor":
            return "inference(factor, [status(thm)], "\
                   +repr(self.parents)+")"    
        elif self.operator == "reference":
            assert(len(self.parents)==1)
            return self.parents[0].name

    def getParents(self):
        """
        Return a list of all derived objects that are used in this
        derivation. 
        """
        if self.operator == "input":
            return []
        elif self.operator == "reference":
            assert(len(self.parents)==1)
            return self.parents
        else:
            res = []
            for p in self.parents:
                res.extend(p.getParents())
            return res
                
        
def flatDerivation(operator, parents):
    """
    Create a derivation which directly references all parents. 
    """
    parentlist = [Derivation("reference", [p]) for p in parents]
    return Derivation(operator, parentlist)
    


class TestDerivations(unittest.TestCase):
    """
    """
    def testDerivable(self):
        """
        Test basic properties of derivations.
        """
        o1 = Derivable()
        o2 = Derivable()
        o3 = Derivable()
        o3.setDerivation(flatDerivation("binres", [o1, o2]))
        self.assertEqual(o1.getParents(),[])
        self.assertEqual(o2.getParents(),[])
        self.assertEqual(len(o3.getParents()), 2)
        print o3
        print o3.derivation
        o3.setDerivation(flatDerivation("factor", [o1]))
        print o3.derivation
        self.assertEqual(len(o3.getParents()), 1)


if __name__ == '__main__':
    unittest.main()
