# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = slheader.S  slsup.S
C_SOURCES = sl.c 

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = ../libcommon/mpsup.o ../libcommon/tpm.o ../libcommon/tpm_emhf.o ../libcommon/pci.o ../libcommon/acpi.o ../libcommon/svm_eap.o ../libcommon/vmx_eap.o ../libcommon/txt_mtrrs.o ../../libemhfc/libemhfc.a

# FIXME: This is a hack.  During build-process refactoring, do
# something more sensible to pickup all in-tree library
# subdirectories.
OBJECTS_PRECOMPILED += ../../libemhfutil/sha1.o
CFLAGS += -I../../libemhfutil/include

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

sl.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) sl.lds.S
	$(LD) -T sl.lds.S -o sl.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
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

