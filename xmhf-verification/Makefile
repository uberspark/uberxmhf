# Makefile for verification
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree operations)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
HYPAPP_VFMS :=

HYPAPP_HYPERDEP := $(srcdir)/../xmhf-slabs/hypapps/xhhyperdep/xhhyperdep.c
HYPAPP_HYPERDEP_DRV := $(srcdir)/driver-xhhyperdep.c
HYPAPP_VFMS += $(srcdir)/../xmhf-slabs/hypapps/xhhyperdep/xhhyperdep-vfm.c

HYPAPP_APPROVEXEC := $(srcdir)/../xmhf-slabs/hypapps/xhapprovexec/xhapprovexec.c
HYPAPP_APPROVEXEC_DRV := $(srcdir)/driver-xhapprovexec.c
#HYPAPP_VFMS += $(srcdir)/../xmhf-slabs/hypapps/xhapprovexec/xhapprovexec-vfm.c

HYPAPP_SYSCALLLOG := $(srcdir)/../xmhf-slabs/hypapps/xhsyscalllog/xhsyscalllog.c
HYPAPP_SYSCALLLOG_DRV := $(srcdir)/driver-xhsyscalllog.c
HYPAPP_VFMS += $(srcdir)/../xmhf-slabs/hypapps/xhsyscalllog/xhsyscalllog-vfm.c

HYPAPP_SSTEPTRACE := $(srcdir)/../xmhf-slabs/hypapps/xhssteptrace/xhssteptrace.c
HYPAPP_SSTEPTRACE_DRV := $(srcdir)/driver-xhssteptrace.c
HYPAPP_VFMS += $(srcdir)/../xmhf-slabs/hypapps/xhssteptrace/xhssteptrace-vfm.c

XMHFCORE_XCIHUB := $(srcdir)/../xmhf-slabs/xmhf-core/xcihub/xcihub.c
XMHFHIC_XCIHUB_DRV := $(srcdir)/driver-xcihub.c


XMHFCORE_XCINIT := $(srcdir)/../xmhf-slabs/xmhf-core/xcinit/xcinit.c
XMHFHIC_XCINIT_DRV := $(srcdir)/driver-xcinit.c


XMHFCORE_XCEXHUB := $(srcdir)/../xmhf-slabs/xmhf-core/xcexhub/xcexhub.c
XMHFHIC_XCEXHUB_DRV := $(srcdir)/driver-xcexhub.c

XMHFHIC_TRAMPOLINE := $(srcdir)/../xmhf-hic/xmhf-hic-rtmcode-trampoline.c
XMHFHIC_TRAMPOLINE_DRV := $(srcdir)/driver-hictrampoline.c

XMHFHIC_SETUP := $(srcdir)/../xmhf-hic/xmhf-hic-setupcode.c
XMHFHIC_SETUP_DATA := $(srcdir)/../xmhf-hic/xmhf-hic-data.c
XMHFHIC_SETUP_DRV := $(srcdir)/driver-hicsetup.c


XMHFHIC_UAPI_CODE := $(srcdir)/../xmhf-hic/xmhf-hic-rtmcode-uapi.c
XMHFHIC_UAPI_DRV := $(srcdir)/driver-uapi.c

XMHFHIC_UAPI_STUB := $(srcdir)/xmhf-hic-rtmcode-uapi-verifstubs.c


.PHONY: all
#all: verifyinit
#all: verifyhypapps
#all: verifyuapi
#all: verifyhictrampoline
#all: verifyhicsetup
all: verifyxcexhub


.PHONY: verifyxcexhub
verifyxcexhub:
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_XCEXHUB_DRV) $(XMHFCORE_XCEXHUB)

.PHONY: verifyhicsetup
verifyhicsetup:
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_SETUP_DRV) $(XMHFHIC_SETUP_DATA) $(XMHFHIC_SETUP)


.PHONY: verifyhictrampoline
verifyhictrampoline:
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_TRAMPOLINE_DRV) $(XMHFHIC_TRAMPOLINE)



.PHONY: verifyinit
verifyinit:
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_STUB) $(XMHFHIC_XCINIT_DRV) $(XMHFCORE_XCINIT)

.PHONY: verifyhypapps
verifyhypapps:
	@echo Verifying hypapps...
	#cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_STUB) $(XMHFHIC_XCIHUB_DRV) $(XMHFCORE_XCIHUB)
	#cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_STUB) $(HYPAPP_VFMS) $(HYPAPP_SSTEPTRACE_DRV) $(HYPAPP_SSTEPTRACE)
	#cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_STUB) $(HYPAPP_VFMS) $(HYPAPP_SYSCALLLOG_DRV) $(HYPAPP_SYSCALLLOG)
	#cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_STUB) $(HYPAPP_VFMS) $(HYPAPP_APPROVEXEC_DRV) $(HYPAPP_APPROVEXEC)
	cbmc --ILP64 --bounds-check --pointer-check -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_STUB) $(HYPAPP_VFMS) $(HYPAPP_HYPERDEP_DRV) $(HYPAPP_HYPERDEP)


.PHONY: verifyuapi
verifyuapi:
	@echo Verifying UAPI...
	cbmc --ILP64 --bounds-check --pointer-check --unwind 10 -D__XMHF_VERIFICATION__ $(VFLAGS) $(XMHFHIC_UAPI_DRV) $(XMHFHIC_UAPI_CODE)


.PHONY: clean
clean:
