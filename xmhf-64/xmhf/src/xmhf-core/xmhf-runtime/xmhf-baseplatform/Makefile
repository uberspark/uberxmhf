# makefile for xmhf-baseplatform (EMHF base platform component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/x86/bplt-x86-$(TARGET_SUBARCH)-smptrampoline.S
AS_SOURCES += ./arch/x86/bplt-x86-$(TARGET_SUBARCH)-smplock.S

C_SOURCES =  bplt-interface.c
C_SOURCES += bplt-interface-runtime.c
C_SOURCES += bplt-interface-smp.c
C_SOURCES += bplt-data.c

C_SOURCES += ./arch/x86/bplt-x86.c
C_SOURCES += ./arch/x86/bplt-x86-data.c
C_SOURCES += ./arch/x86/bplt-x86-pci.c
C_SOURCES += ./arch/x86/bplt-x86-acpi.c
C_SOURCES += ./arch/x86/bplt-x86-pit.c
C_SOURCES += ./arch/x86/bplt-x86-smp.c
C_SOURCES += ./arch/x86/bplt-x86-addressing.c
C_SOURCES += ./arch/x86/bplt-x86-reboot.c
C_SOURCES += ./arch/x86/bplt-x86-cpu.c

C_SOURCES += ./arch/x86/vmx/bplt-x86vmx.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-data.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-vmcs.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-smp.c
ifeq ($(DRT), y)
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-mtrrs-common.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-mtrrs-bootloader.c
endif
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-reboot.c

C_SOURCES += ./arch/x86/svm/bplt-x86svm.c
C_SOURCES += ./arch/x86/svm/bplt-x86svm-data.c
C_SOURCES += ./arch/x86/svm/bplt-x86svm-smp.c

AS_SOURCES_BL =  ./arch/x86/bplt-x86-i386-smplock.S

C_SOURCES_BL =  ./arch/x86/bplt-x86-pci.c
C_SOURCES_BL += ./arch/x86/bplt-x86-acpi.c
C_SOURCES_BL += ./arch/x86/bplt-x86-pit.c
C_SOURCES_BL += ./arch/x86/bplt-x86-addressing.c
C_SOURCES_BL += ./arch/x86/bplt-x86-cpu.c
ifeq ($(DRT), y)
C_SOURCES_BL += ./arch/x86/vmx/bplt-x86vmx-mtrrs-common.c
C_SOURCES_BL += ./arch/x86/vmx/bplt-x86vmx-mtrrs-bootloader.c
endif

# targets
include ../runtime.mk

