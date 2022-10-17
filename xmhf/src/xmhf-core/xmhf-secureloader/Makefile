# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = ./arch/x86/sl-x86-$(TARGET_SUBARCH)-entry.S
AS_SOURCES += ./arch/x86/sl-x86-$(TARGET_SUBARCH)-sup.S

C_SOURCES = sl.c
C_SOURCES += ./arch/x86/sl-x86.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))


#tie components used by SL
OBJECTS_PRECOMPILED = ../xmhf-runtime/xmhf-debug/lib.a

OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/tpm-interface.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/arch/x86/tpm-x86.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/arch/x86/svm/tpm-x86svm.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/arch/x86/vmx/tpm-x86vmx.o

ifeq ($(DMAP), y)
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/dmap-interface-earlyinit.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/dmap-x86-earlyinit.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/svm/dmap-svm.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/vmx/dmap-vmx-earlyinit.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/vmx/dmap-vmx-internal-common.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/vmx/dmap-vmx-internal-earlyinit.o
endif

OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/bplt-x86.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/bplt-x86-pci.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/bplt-x86-acpi.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/bplt-x86-$(TARGET_SUBARCH)-smplock.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/bplt-x86-addressing.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/bplt-x86-cpu.o


OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx.o
ifeq ($(DRT), y)
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-mtrrs-common.o
endif

# separate from OBJECTS_PRECOMPILED becasue needs to come after libs on link line
OBJECTS_PRECOMPILED_LIBBACKENDS = ../xmhf-runtime/xmhf-xmhfcbackend/xmhfc-putchar.o

# FIXME: ADDL_INCLUDES is overly general; sl/ doesn't need all of them
CFLAGS += $(ADDL_INCLUDES)

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# CFLAGS += -fPIC

# RUNTIME_INTEGRITY_HASH should be set by parent Makefile
ifdef RUNTIME_INTEGRITY_HASH
CFLAGS += -D___RUNTIME_INTEGRITY_HASH___=\"$(RUNTIME_INTEGRITY_HASH)\"
endif

# targets
.PHONY: all

all: sl.bin

# FIXME: ADDL_LIBS is overly general; sl/ doesn't need all of them
sl.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) sl.lds
	$(LD) $(LDFLAGS) -T sl.lds -o sl.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	$(CP) sl.exe sl_syms.exe
	$(STRIP) -s sl.exe
	$(OBJCOPY) --output-format=binary sl.exe sl.bin
	# Optional: use sparse file to reduce fs space usage
	-fallocate -d sl.exe
	-fallocate -d sl.bin
	-fallocate -d sl_syms.exe
	# Compute sha-1 hash
	dd if=sl.bin bs=1024 count=64 | sha1sum > sl-below.sha1
	dd if=sl.bin bs=1024 skip=64 count=1984 | sha1sum > sl-above.sha1

sl.lds: sl.lds.S
	gcc -E -x c $(ASFLAGS) $< | grep -v '^#' > $@

.PHONY: clean
clean:
	$(RM) -rf *.o
	$(RM) -rf ./arch/x86/*.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz
	$(RM) -rf *.lds
	$(RM) -rf *.sha1

