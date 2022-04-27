# makefile for xmhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES =  memp-interface.c
C_SOURCES += ./arch/x86/memp-x86.c

C_SOURCES += ./arch/x86/vmx/memp-x86vmx.c
C_SOURCES += ./arch/x86/vmx/memp-x86vmx-data.c

C_SOURCES += ./arch/x86/svm/memp-x86svm.c
C_SOURCES += ./arch/x86/svm/memp-x86svm-data.c

# targets
include ../runtime.mk

