# makefile for libcommon
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = $(wildcard *.S)
C_SOURCES = dbg_printf.c dbg_vgamem.c delay_pit.c txt_mtrrs.c tpm.c tpm_extra.c tpm_emhf.c pci.c acpi.c 

ifeq ($(DEBUG_SERIAL), y)
C_SOURCES += dbg_uart.c
endif

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# FIXME: This is a hack.  During build-process refactoring, do
# something more sensible to pickup all in-tree library
# subdirectories.
CFLAGS += -I../../libemhfutil/include -I../../libemhfc/include

# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
