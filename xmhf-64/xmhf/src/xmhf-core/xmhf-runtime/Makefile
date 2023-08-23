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

OBJECTS_PRECOMPILED += ./xmhf-mm/xmhf-tlsf.o 
OBJECTS_PRECOMPILED += ./xmhf-mm/xmhf-mm.o

OBJECTS_PRECOMPILED += ./xmhf-memprot/memp-interface.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/memp-x86.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/vmx/memp-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/vmx/memp-x86vmx-data.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/vmx/memp-x86vmx-eptlock.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/svm/memp-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/svm/memp-x86svm-data.o
OBJECTS_PRECOMPILED += ./xmhf-memprot/arch/x86/vmx/memp-x86vmx-guestmem.o

OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/svm/peh-x86svm-entry.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/svm/peh-x86svm-main.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86vmx-entry.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86vmx-main.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86-safemsr.o
ifeq ($(UPDATE_INTEL_UCODE), y)
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86vmx-ucode.o
OBJECTS_PRECOMPILED += ./xmhf-eventhub/arch/x86/vmx/peh-x86vmx-ucode-data.o
endif

OBJECTS_PRECOMPILED += ./xmhf-smpguest/smpg-interface.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/smpg-x86.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/svm/smpg-x86svm.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/svm/smpg-x86svm-data.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/vmx/smpg-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-smpguest/arch/x86/vmx/smpg-x86vmx-data.o

ifeq ($(DMAP), y)
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/dmap-interface-runtime.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/iommu-pt.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/dmap-x86-runtime.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/svm/dmap-svm.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-vmx-internal-common.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-vmx-internal-runtime.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-vmx-quirks.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-vmx-runtime.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-vmx-utils.o
OBJECTS_PRECOMPILED += ./xmhf-dmaprot/arch/x86/vmx/dmap-vmx-data.o
endif

OBJECTS_PRECOMPILED += ./xmhf-xcphandler/xcph-interface.o
OBJECTS_PRECOMPILED += ./xmhf-xcphandler/arch/x86/xcph-x86.o
OBJECTS_PRECOMPILED += ./xmhf-xcphandler/arch/x86/xcph-stubs-$(TARGET_SUBARCH).o

OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface-runtime.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-interface-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/bplt-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-pci.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-acpi.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-pit.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-$(TARGET_SUBARCH)-smptrampoline.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-$(TARGET_SUBARCH)-smplock.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-addressing.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-reboot.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/bplt-x86-cpu.o


OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-data.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-smp.o
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-vmcs.o
ifeq ($(DRT), y)
OBJECTS_PRECOMPILED += ./xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-mtrrs-common.o
endif
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
OBJECTS_PRECOMPILED += ./xmhf-startup/arch/x86/rntm-x86-dmap.o

OBJECTS_PRECOMPILED += ./xmhf-debug/lib.a


# separate from OBJECTS_PRECOMPILED because needs to come after libs on link line
OBJECTS_PRECOMPILED_LIBBACKENDS = ./xmhf-xmhfcbackend/xmhfc-putchar.o
OBJECTS_PRECOMPILED_LIBBACKENDS += ./xmhf-xmhfcbackend/stl/xmhfc-bitmap.o
OBJECTS_PRECOMPILED_LIBBACKENDS += ./xmhf-xmhfcbackend/stl/xmhfc-dlist.o

#XMHF memory protection component
RUNTIME_COMPONENTS = xmhf-memprot
#XMHF Memory management component
RUNTIME_COMPONENTS += xmhf-mm
#XMHF partition event-hub component
RUNTIME_COMPONENTS += xmhf-eventhub
#XMHF SMP guest component
RUNTIME_COMPONENTS += xmhf-smpguest
ifeq ($(DMAP), y)
#XMHF DMA protection component
RUNTIME_COMPONENTS += xmhf-dmaprot
endif
#XMHF exception handler component
RUNTIME_COMPONENTS += xmhf-xcphandler
#XMHF base platform component
RUNTIME_COMPONENTS += xmhf-baseplatform
#XMHF partition component
RUNTIME_COMPONENTS += xmhf-partition
#XMHF TPM component
RUNTIME_COMPONENTS += xmhf-tpm
#XMHF debug component
RUNTIME_COMPONENTS += xmhf-debug
#XMHF libxmhfc environment callbacks
RUNTIME_COMPONENTS += xmhf-xmhfcbackend
#XMHF startup component
RUNTIME_COMPONENTS += xmhf-startup

OBJCOPY_FLAGS = --output-format=binary
ifneq ($(SKIP_RUNTIME_BSS), y)
OBJCOPY_FLAGS += --set-section-flags .bss=alloc,load,contents
endif

# targets
.PHONY: runtimecomponents $(RUNTIME_COMPONENTS)
runtimecomponents: $(RUNTIME_COMPONENTS)

$(RUNTIME_COMPONENTS): %:
	cd $@ && $(MAKE) -w all


.PHONY: all
all: runtimecomponents runtime.bin

# Add Makefile dependency to allow parallelize make
$(OBJECTS_PRECOMPILED): %: runtimecomponents
$(OBJECTS_PRECOMPILED_LIBBACKENDS): %: runtimecomponents

runtime.bin: runtimecomponents $(APP_ARCHIVE) runtime.lds
	$(LD) $(LDFLAGS) -T runtime.lds -o runtime.exe $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	# .palign_data and .stack are NOBITS in the ELF file (similar to .bss), but
	# we need them in runtime.bin. So use the --set-section-flags option to
	# force objcopy to zero them and add to runtime.bin. See OBJCOPY_FLAGS
	# above.
	$(OBJCOPY) $(OBJCOPY_FLAGS) runtime.exe runtime.bin
	# Optional: use sparse file for runtime.bin to reduce fs space usage
	-fallocate -d runtime.bin
	# Compute sha-1 hash
	sha1sum runtime.bin > runtime.sha1

runtime.lds: runtime.lds.S
	gcc -E -x c $(ASFLAGS) $< | grep -v '^#' > $@

.PHONY: clean 
clean: 
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz
	$(RM) -rf *.lds
	$(RM) -rf *.sha1

	cd xmhf-mm && $(MAKE) -w clean
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
	cd xmhf-nested && $(MAKE) -w clean
