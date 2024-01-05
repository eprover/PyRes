#!/usr/bin/env python3
# ----------------------------------
#
# Module idents.py

"""
This module provides the facility to create distinct named objects,
similar to e.g. enumerations in C-like languages.

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

import unittest


class Ident:
    """
    Dummy class for generating distinct named objects.
    """

    def __init__(self, name = ""):
        self.name = name

    def __repr__(self):
        return self.name
    

class TestIdents(unittest.TestCase):
    """
    Test collection for idents.
    """       
    def testIdent(self):
        """
        Test that idents work.
        """
        yes  = Ident("yes")
        no   = Ident("no")
        yes2 = Ident("yes")    
        self.assertEqual(yes, yes)
        self.assertEqual(no,no)
        self.assertNotEqual(yes,no)
        self.assertNotEqual(yes,no)
        self.assertNotEqual(yes,yes2)
        self.assertEqual(repr(yes),repr(yes2))
        

if __name__ == '__main__':
    unittest.main()
