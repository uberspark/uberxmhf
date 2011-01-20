# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = slheader.S  slsup.S
C_SOURCES = sl.c 

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = ../libcommon/mpsup.o ../libcommon/string.o ../libcommon/tpm.o ../libcommon/sha1.o

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_vgamem.o
endif

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# CFLAGS += -fPIC

# targets
.PHONY: all
all: $(OBJECTS)
	$(LD) --oformat=pe-i386 --image-base=0x00000000 -T sl.lds.S -o sl.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
	$(CP) sl.exe sl_syms.exe
	$(STRIP) -s sl.exe
	$(OBJCOPY) --input-format=pe-i386 --output-format=binary sl.exe sl.bin

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
	
  
  
  

  
