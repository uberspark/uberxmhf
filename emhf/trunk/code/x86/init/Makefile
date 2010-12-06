# makefile for "init"
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = header.S initsup.S
C_SOURCES = init.c smp.c

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = ../libcommon/mpsup.o ../libcommon/string.o

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_vgamem.o
endif

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)
	$(LD) --oformat=pe-i386 --image-base=0x1E00000 -T init.lds.S -o init.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
	$(CP) init.exe init_syms.exe
	$(STRIP) -s init.exe
	$(OBJCOPY) --input-format=pe-i386 --output-format=binary init.exe init-$(TARGET_HWPLATFORM).bin

%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<
  
.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz
	
  
  
  

  
