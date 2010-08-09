# top-level makefile for runtime
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = runtimesup.S islayersup.S
C_SOURCES = runtime.c islayer.c  apic.c libsechyp.c

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
	$(LD) --oformat=pe-i386 --image-base=0xC0000000 -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
	$(CP) runtime.exe runtime_syms.exe
	$(STRIP) -s runtime.exe
	$(OBJCOPY) --input-format=pe-i386 --output-format=binary runtime.exe runtime.bin

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
	
  
