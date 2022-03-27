# makefile for xmhf-smpguest (EMHF SMP guest component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES =  smpg-interface.c
C_SOURCES += ./arch/x86/smpg-x86.c

C_SOURCES += ./arch/x86/svm/smpg-x86svm.c
C_SOURCES += ./arch/x86/svm/smpg-x86svm-data.c

C_SOURCES += ./arch/x86/vmx/smpg-x86vmx.c
C_SOURCES += ./arch/x86/vmx/smpg-x86vmx-data.c

# targets
include ../runtime.mk

