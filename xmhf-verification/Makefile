# Makefile for verification
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree operations)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))


HYPAPP_HYPERDEP := $(srcdir)/../xmhf-slabs/hypapps/xhhyperdep/xhhyperdep.c
HYPAPP_HYPERDEP_DRV := $(srcdir)/driver-xhhyperdep.c

XMHFHIC_UAPI_CODE := $(srcdir)/../xmhf-hic/xmhf-hic-rtmcode-uapi.c
XMHFHIC_UAPI_DRV := $(srcdir)/driver-uapi.c



.PHONY: all
#all: verifyhypapps
all: verifyuapi

.PHONY: verifyhypapps
verifyhypapps:
	@echo Verifying hypapps...
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(HYPAPP_HYPERDEP_DRV) $(HYPAPP_HYPERDEP)

.PHONY: verifyuapi
verifyuapi:
	@echo Verifying UAPI...
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_DRV) $(XMHFHIC_UAPI_CODE)


.PHONY: clean
clean:
