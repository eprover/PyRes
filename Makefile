#------------------------------------------------------------------------
#
# File  : Makefile for PyRes.
#
# Author: Stephan Schulz
#
#------------------------------------------------------------------------

STAREXECPATH=$(HOME)/StarExec
VERSION=v2.0.11

CONFIG_SUB_FOLDERS = default sos0 sos1 sos2 sos3

all:

clean:
	-rm -f *.pyc *~

distrib: clean
	cd ..; tar czf PyRes.tgz PyRes

starexec: clean
	echo $(STAREXECPATH)
	rm -rf $(STAREXECPATH)/bin
	mkdir -p $(STAREXECPATH)/bin
	find . -name ".#*"  -exec rm {} \;
	cp *.py $(STAREXECPATH)/bin
	for config in $(CONFIGS) ; do \
		cp starexec_run_PyRes_$$config $(STAREXECPATH)/bin ; \
	done

	for subfolder in $(CONFIG_SUB_FOLDERS) ; do \
		cp ./config/$$subfolder/* ${STAREXECPATH}/bin ; \
	done

	cd $(STAREXECPATH); zip -r PyRes_$(VERSION).zip bin

