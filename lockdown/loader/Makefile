################################################################################
# intel vt vmm with v86 monitor
# author: amit vasudevan (amitvasudevan@acm.org)
#
# makefile for loader
#
# history:
# 10/2/2009 12:35:07 PM  - initial version

# source files
AS_SOURCES = entry.S
C_SOURCES = loader.c 

ifeq ($(CONF_GUESTOS_LINUX), y)
C_SOURCES += linuxrelc.c 
AS_SOURCES += linuxrelcsup.S
endif

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = $(wildcard ../common/*.o)

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../debug/printf.o ../debug/uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../debug/printf.o ../debug/vgamem.o
endif

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)
	$(LD) --oformat=pe-i386 --image-base=0x1E00000 -T loader.lds.S -o loader.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
	$(CP) loader.exe loader_syms.exe
	$(STRIP) -s loader.exe
	$(OBJCOPY) --input-format=pe-i386 --output-format=binary loader.exe loader.bin
	$(RM) -rf loader.exe
	
%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<
  
.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	
  
  
  

  
