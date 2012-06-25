# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = ./arch/x86/sl-x86-entry.S  
AS_SOURCES += ./arch/x86/sl-x86-sup.S

C_SOURCES = sl.c 
C_SOURCES += ./arch/x86/sl-x86.c 


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))


#tie components used by SL
OBJECTS_PRECOMPILED = ../xmhf-debug/lib.a

OBJECTS_PRECOMPILED += ../xmhf-tpm/tpm-interface.o 
OBJECTS_PRECOMPILED += ../xmhf-tpm/arch/x86/tpm-x86.o 
OBJECTS_PRECOMPILED += ../xmhf-tpm/arch/x86/svm/tpm-x86svm.o 
OBJECTS_PRECOMPILED += ../xmhf-tpm/arch/x86/vmx/tpm-x86vmx.o 


OBJECTS_PRECOMPILED += ../xmhf-dmaprot/dmap-interface.o 
OBJECTS_PRECOMPILED += ../xmhf-dmaprot/arch/x86/dmap-x86.o 
OBJECTS_PRECOMPILED += ../xmhf-dmaprot/arch/x86/svm/dmap-x86svm.o 
OBJECTS_PRECOMPILED += ../xmhf-dmaprot/arch/x86/vmx/dmap-x86vmx.o

OBJECTS_PRECOMPILED += ../xmhf-baseplatform/bplt-interface.o
OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/bplt-x86.o
OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/bplt-x86-pci.o
OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/bplt-x86-acpi.o
OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/bplt-x86-smplock.o
OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/bplt-x86-addressing.o

OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx.o
OBJECTS_PRECOMPILED += ../xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-mtrrs.o

# separate from OBJECTS_PRECOMPILED becasue needs to come after libs on link line
OBJECTS_PRECOMPILED_LIBBACKENDS = ../xmhf-xmhfcbackend/xmhfc-putchar.o

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
sl.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) sl.lds.S
	$(LD) -T sl.lds.S -o sl.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	$(CP) sl.exe sl_syms.exe
	$(STRIP) -s sl.exe
	$(OBJCOPY) --output-format=binary sl.exe sl.bin

%.o: %.S $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf ./arch/x86/*.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz

