# makefile for xmhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES =  dmap-interface-earlyinit.c
C_SOURCES += dmap-interface-runtime.c
C_SOURCES += iommu-pt.c
C_SOURCES += ./arch/x86/dmap-x86-earlyinit.c
C_SOURCES += ./arch/x86/dmap-x86-runtime.c
C_SOURCES += ./arch/x86/svm/dmap-svm.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-earlyinit.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-internal-common.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-internal-runtime.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-quirks.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-runtime.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-utils.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-data.c

# targets
include ../runtime.mk

