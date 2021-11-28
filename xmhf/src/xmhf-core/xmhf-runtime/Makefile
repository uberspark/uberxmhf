# makefile for "runtime"
# author: amit vasudevan (amitvasudevan@acm.org)

# tie components used by the runtime
# WARNING: if both Serial & VGA are enabled, you actually get neither. 
# TODO: Fix it.
# OBJECTS_PRECOMPILED = ./xmhf-debug/lib.a

# OBJECTS_PRECOMPILED += ./xmhf-tpm/tpm-interface.o 
OBJECTS_PRECOMPILED = ./xmhf-tpm/tpm-interface.o 
OBJECTS_PRECOMPILED += ./xmhf-tpm/arch/$(TARGET_HWPLATFORM)/tpm-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-tpm/arch/$(TARGET_HWPLATFORM)/svm/tpm-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ./xmhf-tpm/arch/$(TARGET_HWPLATFORM)/vmx/tpm-$(TARGET_HWPLATFORM)vmx.o


OBJECTS_PRECOMPILED += ./xmhf-memprot/memp-interface.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/$(TARGET_HWPLATFORM)/memp-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/$(TARGET_HWPLATFORM)/vmx/memp-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/$(TARGET_HWPLATFORM)/vmx/memp-$(TARGET_HWPLATFORM)vmx-data.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/$(TARGET_HWPLATFORM)/svm/memp-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/$(TARGET_HWPLATFORM)/svm/memp-$(TARGET_HWPLATFORM)svm-data.o

OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/$(TARGET_HWPLATFORM)/svm/peh-$(TARGET_HWPLATFORM)svm-entry.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/$(TARGET_HWPLATFORM)/svm/peh-$(TARGET_HWPLATFORM)svm-main.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/$(TARGET_HWPLATFORM)/vmx/peh-$(TARGET_HWPLATFORM)vmx-entry.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/$(TARGET_HWPLATFORM)/vmx/peh-$(TARGET_HWPLATFORM)vmx-main.o

OBJECTS_PRECOMPILED += ./xmhf-smpguest/smpg-interface.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/$(TARGET_HWPLATFORM)/smpg-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/$(TARGET_HWPLATFORM)/svm/smpg-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/$(TARGET_HWPLATFORM)/svm/smpg-$(TARGET_HWPLATFORM)svm-data.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/$(TARGET_HWPLATFORM)/vmx/smpg-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/$(TARGET_HWPLATFORM)/vmx/smpg-$(TARGET_HWPLATFORM)vmx-data.o

OBJECTS_PRECOMPILED += ./xmhf-dmaprot/dmap-interface.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/dmap-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/svm/dmap-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/vmx/dmap-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/vmx/dmap-$(TARGET_HWPLATFORM)vmx-data.o

OBJECTS_PRECOMPILED += ./xmhf-xcphandler/xcph-interface.o
OBJECTS_PRECOMPILED += ./xmhf-xcphandler/arch/$(TARGET_HWPLATFORM)/xcph-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-xcphandler/arch/$(TARGET_HWPLATFORM)/xcph-stubs.o

OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-pci.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-acpi.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-pit.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smptrampoline.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smplock.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-addressing.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-reboot.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-cpu.o


OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-vmcs.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-mtrrs.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-reboot.o


OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm-smp.o


OBJECTS_PRECOMPILED += ./xmhf-partition/part-interface.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/$(TARGET_HWPLATFORM)/part-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/$(TARGET_HWPLATFORM)/svm/part-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/$(TARGET_HWPLATFORM)/svm/part-$(TARGET_HWPLATFORM)svm-sup.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/$(TARGET_HWPLATFORM)/vmx/part-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ./xmhf-partition/arch/$(TARGET_HWPLATFORM)/vmx/part-$(TARGET_HWPLATFORM)vmx-sup.o

OBJECTS_PRECOMPILED += ./xmhf-startup/runtime.o
OBJECTS_PRECOMPILED += ./xmhf-startup/rntm-data.o
OBJECTS_PRECOMPILED += ./xmhf-startup/arch/$(TARGET_HWPLATFORM)/rntm-$(TARGET_HWPLATFORM)-data.o

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

# Add Makefile dependency to allow parallelize make
$(OBJECTS_PRECOMPILED): %: runtimecomponents
$(OBJECTS_PRECOMPILED_LIBBACKENDS): %: runtimecomponents

runtime.bin: runtimecomponents $(APP_ARCHIVE) runtime-$(TARGET_HWPLATFORM).lds.S
	$(LD) -T runtime-$(TARGET_HWPLATFORM).lds.S -o runtime.exe $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
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
