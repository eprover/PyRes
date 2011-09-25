#------------------------------------------------------------------------
#
# File  : Makefile for FOD-PI example prover.
#
# Author: Stephan Schulz
#
# Changes
#
# <1> Mon Sep 19 13:50:35 CEST 2011
#     New
#
#------------------------------------------------------------------------


all: 

clean:	
	-rm *.pyc *~


testcov: *.py
	-rm -r .coverage COVERAGE
	for f in *.py ;do coverage run -a $$f; done
	coverage report > testcov
	mkdir COVERAGE
	coverage annotate -d COVERAGE
	cat testcov


tags: TAGS

TAGS: *.py
	etags *.py
