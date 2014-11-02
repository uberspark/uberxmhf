# Makefile for verification
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree operations)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))


HYPAPP_HYPERDEP := $(srcdir)/../xmhf-slabs/hypapps/xhhyperdep/xhhyperdep.c

.PHONY: all
all: verifyhypapps

.PHONY: verifyhypapps
verifyhypapps:
	@echo Verifying hypapps...


.PHONY: clean
clean:
