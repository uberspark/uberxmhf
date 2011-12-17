# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = slheader.S  slsup.S
C_SOURCES = sl.c 

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = ../libcommon/mpsup.o ../libcommon/tpm.o ../libcommon/tpm_emhf.o ../libcommon/pci.o ../libcommon/acpi.o ../libcommon/txt_mtrrs.o
OBJECTS_PRECOMPILED += ../components/emhf-dmaprot/dmap-interface.o ../components/emhf-dmaprot/arch/x86/svm/dmap-x86svm.o ../components/emhf-dmaprot/arch/x86/vmx/dmap-x86vmx.o
# FIXME: ADDL_INCLUDES is overly general; sl/ doesn't need all of them
CFLAGS += $(ADDL_INCLUDES)

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_vgamem.o
endif

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
	$(LD) -T sl.lds.S -o sl.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(ADDL_LIBS)
	$(CP) sl.exe sl_syms.exe
	$(STRIP) -s sl.exe
	$(OBJCOPY) --output-format=binary sl.exe sl.bin

%.o: %.S $(I_SOURCES) Makefile ../Makefile	../../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile	../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz

