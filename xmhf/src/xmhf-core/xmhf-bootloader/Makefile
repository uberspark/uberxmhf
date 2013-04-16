# makefile for "init"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = header.S initsup.S
C_SOURCES = init.c smp.c txt_heap.c txt_hash.c txt_acmod.c txt.c cmdline.c

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = ../components/xmhf-debug/lib.a

OBJECTS_PRECOMPILED += ../components/xmhf-tpm/tpm-interface.o 
OBJECTS_PRECOMPILED += ../components/xmhf-tpm/arch/x86/tpm-x86.o 
OBJECTS_PRECOMPILED += ../components/xmhf-tpm/arch/x86/svm/tpm-x86svm.o 
OBJECTS_PRECOMPILED += ../components/xmhf-tpm/arch/x86/vmx/tpm-x86vmx.o 

OBJECTS_PRECOMPILED += ../components/xmhf-baseplatform/arch/x86/bplt-x86-pci.o
OBJECTS_PRECOMPILED += ../components/xmhf-baseplatform/arch/x86/bplt-x86-acpi.o
OBJECTS_PRECOMPILED += ../components/xmhf-baseplatform/arch/x86/bplt-x86-smplock.o
OBJECTS_PRECOMPILED += ../components/xmhf-baseplatform/arch/x86/bplt-x86-addressing.o

OBJECTS_PRECOMPILED += ../components/xmhf-baseplatform/arch/x86/vmx/bplt-x86vmx-mtrrs.o

# FIXME: This is overly general; init/ doesn't need all of these
CFLAGS += $(ADDL_INCLUDES)

# separate from OBJECTS_PRECOMPILED becasue needs to come after libs on link line
OBJECTS_PRECOMPILED_LIBBACKENDS = ../components/xmhf-xmhfcbackend/xmhfc-putchar.o

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)


# NOTE: THIS IS THE init MODULE.  IT IS COMPLETELY UNTRUSTED.  THESE
# VALUES ARE HERE SIMPLY TO AID IN DEVELOPMENT AND DEBUGGING, TO STOP
# EARLY IN THE EVENT OF MISTAKES.  DO NOT RELY ON THEM!

# RUNTIME_INTEGRITY_HASH should be set by parent Makefile
ifdef RUNTIME_INTEGRITY_HASH
CFLAGS += -D___RUNTIME_INTEGRITY_HASH___=\"$(RUNTIME_INTEGRITY_HASH)\"
endif
# SLABOVE64K_INTEGRITY_HASH should be set by parent Makefile
ifdef SLABOVE64K_INTEGRITY_HASH
CFLAGS += -D___SLABOVE64K_INTEGRITY_HASH___=\"$(SLABOVE64K_INTEGRITY_HASH)\"
endif
# SLBELOW64K_INTEGRITY_HASH should be set by parent Makefile
ifdef SLBELOW64K_INTEGRITY_HASH
CFLAGS += -D___SLBELOW64K_INTEGRITY_HASH___=\"$(SLBELOW64K_INTEGRITY_HASH)\"
endif


# targets
.PHONY: all
all: init-$(TARGET_HWPLATFORM).bin

# FIXME: ADDL_LIBS is overly general; init/ doesn't need all of them
init-$(TARGET_HWPLATFORM).bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) init.lds.S
	$(LD) -T init.lds.S -o init.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	$(CP) init.exe init_syms.exe
	$(STRIP) -s init.exe
	$(OBJCOPY) --output-format=binary init.exe init-$(TARGET_HWPLATFORM).bin

%.o: %.S $(I_SOURCES) Makefile ../Makefile  ../../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile	../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz

