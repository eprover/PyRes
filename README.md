# PyRes

This code implements simple, resolution-based theorem provers for
first-order logic. It is released as free software under the GNU GPL
version 2, and without any warranty. See the file COPYING for
details, and the individual source headers for copyright information.

## Prerequisites

Python version 3.4 or higher is required to run PyRes. Check your version with one of the following commands.

```
python --version
python3 --version
```
You might try the uppercase variants `Python` or `Python3` if the commands don't get recognized.

It is sufficient if at least one of the versions high enough. In the following code snippets you should choose the 
command that works on your machine.

If the commands don't get recognized, or the version is too old, see https://www.python.org/downloads/ for more
information how to install. 

## Install PyRes

Just clone the repository into a new directory, with
```
git clone https://github.com/eprover/PyRes.git
```
Alternatively, you can download the .ZIP file from GitHub and extract it locally.

No futher installation should be necessary.

## Run PyRes

To run PyRes, you should open a terminal and change the current directory to the root folder of the project.
Afterwards, you can choose one of the following 3 scripts to execute.

### pyres-simple.py

This is the simplest example of a prover for the clausal fragment of
first-order logic. It implements the basic given-clause loop with
first-in-first-out clause selection and without any redundancy
elimination.

Suggested command line
```
python3 pyres-simple.py EXAMPLES/PUZ002-1.p
```

PUZ001-1.p is quite hard for pyres-simple!


### pyres-cnf.py

This version of the prover processes the same logic as
pyres-simple.py, but adds some performance-enhancing features. This
include better clause selection heuristics, subsumption, and negative
literal selection.

Suggested command line:
```
python3 pyres-cnf.py -tfb -HPickGiven5 -nsmallest EXAMPLES/PUZ001-1.p
```

### pyres-fof.py

This prover adds a simple clausifier, so it is able to process full
first-order logic. It also will detect the use of equality, and add
equality axioms. Otherwise, it is similar to pyres-cnf.py.


Suggested command line:
```
python3 pyres-fof.py -tifbp -HPickGiven5 -nlargest EXAMPLES/PUZ001+1.p
```

## Run Unittests

To execute the unit tests, run 

`python3 -m unittest`

The unittest module automatically discovers all the testcases and executes them. 

## Run Unittests with Coverage

Install the python coverage module with:

`pip install coverage`

Check if it is installed correctly with:

`coverage --version`

If the command does not get recognized by your machine, 
check the following guide https://coverage.readthedocs.io/en/6.4.1/install.html.

Afterwards, you can run 

`coverage run unittest`

This executes the unittests and generates a .coverage file. To print a summary in the terminal run:

`coverage report`

Alternatively, you can generate .HTML files with the exact coverage with 

`coverage html`

See https://coverage.readthedocs.io/en/6.4.1/cmd.html#cmd-report for additional information.

## Information on StarExec

This section requires Make and only works on UNIX-based operating systems.

To run jobs on StarExec, you need to upload a solver as a .ZIP file.
The following command allows you to generate a .ZIP file with all the
necessary Python files inside.

`make starexec`

This creates a .ZIP file named "StarExec_$(version).zip" in the folder $(HOME)/StarExec.
The version and the directory can be customized in the Makefile.

The .ZIP file does not only include Python files but also configurations
that specify e.g., selected optimizations.

In the Makefile you can also specify which configurations should be included in the .ZIP file.

## Result in the Output

### Status

Problem is CNF and unsatisfiable: `SZS status Unsatisfiable`

Problem is CNF and satisfiable: `SZS status Satisfiable`

Problem is FOF and a theorem: `SZS status Theorem`

Problem is FOF and not a theorem: `SZS status CounterSatisfiable`

### Refutation

The start of solution output for proofs: `SZS output start CNFRefutation.`

The end of solution output for proofs: `SZS output end CNFRefutation.`

The start of solution output for models/saturations: `SZS output start Saturation.`

The end of solution output for models/saturations: `SZS output end Saturation.`
