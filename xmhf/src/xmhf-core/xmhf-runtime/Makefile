# makefile for "runtime"
# author: amit vasudevan (amitvasudevan@acm.org)

# tie components used by the runtime
# WARNING: if both Serial & VGA are enabled, you actually get neither. 
# TODO: Fix it.
# OBJECTS_PRECOMPILED = ./xmhf-debug/lib.a

# OBJECTS_PRECOMPILED += ./xmhf-tpm/tpm-interface.o 
OBJECTS_PRECOMPILED = ./xmhf-tpm/tpm-interface.o 
OBJECTS_PRECOMPILED += ./xmhf-tpm/arch/x86/tpm-x86.o 
OBJECTS_PRECOMPILED += ./xmhf-tpm/arch/x86/svm/tpm-x86svm.o 
OBJECTS_PRECOMPILED += ./xmhf-tpm/arch/x86/vmx/tpm-x86vmx.o 


OBJECTS_PRECOMPILED += ./xmhf-memprot/memp-interface.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/memp-x86.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/vmx/memp-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/vmx/memp-x86vmx-data.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/svm/memp-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/svm/memp-x86svm-data.o

OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/svm/peh-x86svm-entry.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/svm/peh-x86svm-main.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86vmx-entry.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86vmx-main.o

OBJECTS_PRECOMPILED += ./xmhf-smpguest/smpg-interface.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/smpg-x86.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/svm/smpg-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/svm/smpg-x86svm-data.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/vmx/smpg-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/vmx/smpg-x86vmx-data.o

OBJECTS_PRECOMPILED += ./xmhf-dmaprot/dmap-interface.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/dmap-x86.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/svm/dmap-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-x86vmx-data.o

OBJECTS_PRECOMPILED += ./xmhf-xcphandler/xcph-interface.o
OBJECTS_PRECOMPILED += ./xmhf-xcphandler/arch/x86/xcph-x86.o
OBJECTS_PRECOMPILED += ./xmhf-xcphandler/arch/x86/xcph-stubs.o

OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-pci.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-acpi.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-pit.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-smptrampoline.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-smplock.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-addressing.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-reboot.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-cpu.o


OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-vmcs.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-mtrrs.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-reboot.o


OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/svm/bplt-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/svm/bplt-x86svm-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/svm/bplt-x86svm-smp.o


OBJECTS_PRECOMPILED += ./xmhf-partition/part-interface.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/x86/part-x86.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/x86/svm/part-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/x86/svm/part-x86svm-sup.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/x86/vmx/part-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/x86/vmx/part-x86vmx-sup.o

OBJECTS_PRECOMPILED += ./xmhf-startup/runtime.o
OBJECTS_PRECOMPILED += ./xmhf-startup/rntm-data.o
OBJECTS_PRECOMPILED += ./xmhf-startup/arch/x86/rntm-x86-data.o

OBJECTS_PRECOMPILED += ./xmhf-debug/lib.a


# separate from OBJECTS_PRECOMPILED becasue needs to come after libs on link line
OBJECTS_PRECOMPILED_LIBBACKENDS = ./xmhf-xmhfcbackend/xmhfc-putchar.o


# targets
.PHONY: runtimecomponents
runtimecomponents:
	#XMHF memory protection component
	cd xmhf-memprot && $(MAKE) -w all
	#XMHF partition event-hub component
	cd xmhf-eventhub && $(MAKE) -w all
	#XMHF SMP guest component
	cd xmhf-smpguest && $(MAKE) -w all
	#XMHF DMA protection component
	cd xmhf-dmaprot && $(MAKE) -w all
	#XMHF exception handler component
	cd xmhf-xcphandler && $(MAKE) -w all
	#XMHF base platform component
	cd xmhf-baseplatform && $(MAKE) -w all
	#XMHF partition component
	cd xmhf-partition && $(MAKE) -w all
	#XMHF TPM component
	cd xmhf-tpm && $(MAKE) -w all
	#XMHF debug component
	cd xmhf-debug && $(MAKE) -w all
	#XMHF libxmhfc environment callbacks
	cd xmhf-xmhfcbackend && $(MAKE) -w all
	#XMHF startup component
	cd xmhf-startup && $(MAKE) -w all


.PHONY: all
all: runtimecomponents runtime.bin

runtime.bin: runtimecomponents $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(OBJECTS_PRECOMPILED_LIBBACKENDS) runtime.lds.S
	$(LD) -T runtime.lds.S -o runtime.exe $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	$(OBJCOPY) --output-format=binary runtime.exe runtime.bin

%.o: %.S $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../../Makefile 
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz

	cd xmhf-memprot && $(MAKE) -w clean
	cd xmhf-eventhub && $(MAKE) -w clean
	cd xmhf-dmaprot && $(MAKE) -w clean
	cd xmhf-smpguest && $(MAKE) -w clean
	cd xmhf-xcphandler && $(MAKE) -w clean
	cd xmhf-baseplatform && $(MAKE) -w clean
	cd xmhf-partition && $(MAKE) -w clean
	cd xmhf-tpm && $(MAKE) -w clean
	cd xmhf-debug && $(MAKE) -w clean
	cd xmhf-xmhfcbackend && $(MAKE) -w clean
	cd xmhf-startup && $(MAKE) -w clean
