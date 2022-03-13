# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = ./arch/$(TARGET_HWPLATFORM)/sl-$(TARGET_HWPLATFORM)-entry.S
AS_SOURCES += ./arch/$(TARGET_HWPLATFORM)/sl-$(TARGET_HWPLATFORM)-sup.S

C_SOURCES = sl.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/sl-$(TARGET_HWPLATFORM).c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))


#tie components used by SL
OBJECTS_PRECOMPILED = ../xmhf-runtime/xmhf-debug/lib.a

OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/tpm-interface.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/arch/$(TARGET_HWPLATFORM)/tpm-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/arch/$(TARGET_HWPLATFORM)/svm/tpm-$(TARGET_HWPLATFORM)svm.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-tpm/arch/$(TARGET_HWPLATFORM)/vmx/tpm-$(TARGET_HWPLATFORM)vmx.o


OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/dmap-interface-earlyinit.o
# OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/dmap-$(TARGET_HWPLATFORM).o
# OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/svm/dmap-$(TARGET_HWPLATFORM)svm.o
# OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/$(TARGET_HWPLATFORM)/vmx/dmap-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/dmap-x86-earlyinit.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/svm/dmap-svm.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/vmx/dmap-vmx-earlyinit.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-dmaprot/arch/x86/vmx/dmap-vmx-internal.o

OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM).o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-pci.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-acpi.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smplock.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-addressing.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-cpu.o


OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx.o
OBJECTS_PRECOMPILED += ../xmhf-runtime/xmhf-baseplatform/arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-mtrrs.o

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
sl.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) sl-$(TARGET_HWPLATFORM).lds.S
	$(LD) -T sl-$(TARGET_HWPLATFORM).lds.S -o sl.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	$(CP) sl.exe sl_syms.exe
	$(STRIP) -s sl.exe
	$(OBJCOPY) --output-format=binary sl.exe sl.bin
	# Optional: use sparse file to reduce fs space usage
	fallocate -d sl.exe
	fallocate -d sl.bin
	fallocate -d sl_syms.exe

%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) -rf *.o
	$(RM) -rf ./arch/*/*.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz

