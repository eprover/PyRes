"""
A simple lexical analyser that converts a string into a sequence of
tokens.

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


class ScannerError(Exception):
    """
    A class representing all errors that the scanner can produce.
    """

    def __init__(self):
        self.name = "ScannerError"
        self.value = "<none>"

    def __repr__(self):
        return self.name + "(" + repr(self.value) + ")"

    def __str__(self):
        return self.__repr__()


class IllegalCharacterError(ScannerError):
    """
    Class representing an unexpexted character error
    """

    def __init__(self, char):
        self.name = "Illegal character"
        self.value = char


class UnexpectedTokenError(ScannerError):
    """
    Class representing an unexpected token error.
    """

    def __init__(self, token):
        self.name = "Unexpected token"
        self.value = token


class UnexpectedIdentError(ScannerError):
    """
    Class representing an unexpected identifier error.
    """

    def __init__(self, token):
        self.name = "Unexpected identifier"
        self.value = token
