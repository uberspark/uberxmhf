# top-level makefile for runtime
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = runtimesup.S 
C_SOURCES = runtime.c globals.c 
C_SOURCES += rntm-data.c

C_SOURCES += ./arch/x86/rntm-x86-data.c

# These are the core runtime objects
OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))


# tie components used by the runtime
# WARNING: if both Serial & VGA are enabled, you actually get neither. 
# TODO: Fix it.
OBJECTS_PRECOMPILED = ../emhf-debug/dbg-interface.o

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../emhf-debug/arch/x86/dbg-x86-uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../emhf-debug/arch/x86/dbg-x86-vgamem.o
endif

OBJECTS_PRECOMPILED += ../emhf-tpm/tpm.o
OBJECTS_PRECOMPILED += ../emhf-tpm/tpm_emhf.o
OBJECTS_PRECOMPILED += ../emhf-tpm/tpm_extra.o


OBJECTS_PRECOMPILED += ../emhf-memprot/memp-interface.o
OBJECTS_PRECOMPILED += ../emhf-memprot/arch/x86/memp-x86.o
OBJECTS_PRECOMPILED += ../emhf-memprot/arch/x86/vmx/memp-x86vmx.o
OBJECTS_PRECOMPILED += ../emhf-memprot/arch/x86/svm/memp-x86svm.o

OBJECTS_PRECOMPILED += ../emhf-parteventhub/arch/x86/svm/peh-x86svm-entry.o
OBJECTS_PRECOMPILED += ../emhf-parteventhub/arch/x86/svm/peh-x86svm-main.o
OBJECTS_PRECOMPILED += ../emhf-parteventhub/arch/x86/vmx/peh-x86vmx-entry.o
OBJECTS_PRECOMPILED += ../emhf-parteventhub/arch/x86/vmx/peh-x86vmx-main.o

OBJECTS_PRECOMPILED += ../emhf-smpguest/smpg-interface.o
OBJECTS_PRECOMPILED += ../emhf-smpguest/arch/x86/smpg-x86.o
OBJECTS_PRECOMPILED += ../emhf-smpguest/arch/x86/svm/smpg-x86svm.o
OBJECTS_PRECOMPILED += ../emhf-smpguest/arch/x86/vmx/smpg-x86vmx.o

OBJECTS_PRECOMPILED += ../emhf-dmaprot/dmap-interface.o
OBJECTS_PRECOMPILED += ../emhf-dmaprot/arch/x86/dmap-x86.o
OBJECTS_PRECOMPILED += ../emhf-dmaprot/arch/x86/svm/dmap-x86svm.o
OBJECTS_PRECOMPILED += ../emhf-dmaprot/arch/x86/vmx/dmap-x86vmx.o
OBJECTS_PRECOMPILED += ../emhf-dmaprot/arch/x86/vmx/dmap-x86vmx-data.o

OBJECTS_PRECOMPILED += ../emhf-xcphandler/xcph-interface.o
OBJECTS_PRECOMPILED += ../emhf-xcphandler/arch/x86/xcph-x86.o
OBJECTS_PRECOMPILED += ../emhf-xcphandler/arch/x86/xcph-stubs.o

OBJECTS_PRECOMPILED += ../emhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/bplt-interface-smp.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-pci.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-acpi.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-pit.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-smp.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-smptrampoline.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-smplock.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-addressing.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/bplt-x86-reboot.o

OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/vmx/bplt-x86vmx.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/vmx/bplt-x86vmx-smp.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/vmx/bplt-x86vmx-vmcs.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/vmx/bplt-x86vmx-mtrrs.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/vmx/bplt-x86vmx-reboot.o


OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/svm/bplt-x86svm.o
OBJECTS_PRECOMPILED += ../emhf-baseplatform/arch/x86/svm/bplt-x86svm-smp.o


OBJECTS_PRECOMPILED += ../emhf-partition/part-interface.o
OBJECTS_PRECOMPILED += ../emhf-partition/arch/x86/part-x86.o
OBJECTS_PRECOMPILED += ../emhf-partition/arch/x86/svm/part-x86svm.o
OBJECTS_PRECOMPILED += ../emhf-partition/arch/x86/svm/part-x86svm-sup.o
OBJECTS_PRECOMPILED += ../emhf-partition/arch/x86/vmx/part-x86vmx.o
OBJECTS_PRECOMPILED += ../emhf-partition/arch/x86/vmx/part-x86vmx-sup.o

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: runtime.bin

runtime.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) runtime.lds.S
	$(LD) -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(ADDL_LIBS)
	$(OBJCOPY) --output-format=binary runtime.exe runtime.bin

%.o: %.S $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../../Makefile 
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz


