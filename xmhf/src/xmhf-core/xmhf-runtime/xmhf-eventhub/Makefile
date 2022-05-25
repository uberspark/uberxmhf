# makefile for xmhf-parteventhub (EMHF partition event-hub component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/x86/svm/peh-x86-$(TARGET_SUBARCH)svm-entry.S
AS_SOURCES += ./arch/x86/vmx/peh-x86-$(TARGET_SUBARCH)vmx-entry.S

C_SOURCES =  ./arch/x86/svm/peh-x86svm-main.c
C_SOURCES += ./arch/x86/vmx/peh-x86vmx-main.c
C_SOURCES += ./arch/x86/vmx/peh-x86-safemsr.c
C_SOURCES += ./arch/x86/vmx/peh-x86vmx-guestmem.c
ifeq ($(UPDATE_INTEL_UCODE), y)
C_SOURCES += ./arch/x86/vmx/peh-x86vmx-ucode.c
C_SOURCES += ./arch/x86/vmx/peh-x86vmx-ucode-data.c
endif
ifeq ($(NESTED_VIRTUALIZATION), y)
C_SOURCES += ./arch/x86/vmx/peh-x86vmx-nested.c
endif

# targets
include ../runtime.mk

