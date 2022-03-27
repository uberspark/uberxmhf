# makefile for EMHF TPM component
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES =  tpm-interface.c
C_SOURCES += ./arch/x86/tpm-x86.c
C_SOURCES += ./arch/x86/svm/tpm-x86svm.c
C_SOURCES += ./arch/x86/vmx/tpm-x86vmx.c

C_SOURCES_BL =  tpm-interface.c
C_SOURCES_BL += ./arch/x86/tpm-x86.c
C_SOURCES_BL += ./arch/x86/svm/tpm-x86svm.c
C_SOURCES_BL += ./arch/x86/vmx/tpm-x86vmx.c

# targets
include ../runtime.mk

