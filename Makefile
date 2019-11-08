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

STAREXECPATH=$(HOME)/StarExec

all:

clean:
	-rm -f *.pyc *~


testcov: *.py
	-rm -r .coverage COVERAGE
	for f in *.py ;do coverage-3.7 run -a $$f; done
	coverage-3.7 report > testcov
	mkdir COVERAGE
	coverage-3.7 annotate -d COVERAGE
	cat testcov


tags: TAGS

TAGS: *.py
	etags *.py



distrib: clean
	cd ..; tar czf PyRes.tgz PyRes

starexec:
	echo $(STAREXECPATH)
	rm -rf $(STAREXECPATH)
	mkdir -p $(STAREXECPATH)/bin
	find . -name ".#*"  -exec rm {} \;
	cp *.py starexec_run_* $(STAREXECPATH)/bin
	cp README $(STAREXECPATH)
	cd $(STAREXECPATH); zip -r PyRes.zip bin
