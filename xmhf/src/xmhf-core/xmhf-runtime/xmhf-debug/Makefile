# makefile for EMHF debug component
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 

C_SOURCES = dbg-interface.c 
C_SOURCES += ./arch/x86/emhf_debug_arch.c

ifeq ($(DEBUG_SERIAL), y)
C_SOURCES += ./arch/x86/dbg-x86-uart.c
endif

ifeq ($(DEBUG_VGA), y)
C_SOURCES += ./arch/x86/dbg-x86-vgamem.c
endif

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_WORDSIZE), amd64)
C_OBJECTS32 = $(patsubst %.c, %.x86.o, $(C_SOURCES))
OBJECTS32 = $(C_OBJECTS32)
endif

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: lib.a

lib.a: $(OBJECTS)
	$(AR) rvs $@ $^

%.o: %.S $(I_SOURCES) Makefile ../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_WORDSIZE), amd64)
all: lib.x86.a

lib.x86.a: $(OBJECTS32)
	$(AR) rvs $@ $^
$(C_OBJECTS32): %.x86.o: %.c $(I_SOURCES) Makefile ../Makefile ../../Makefile
	$(CC32) -c $(BCFLAGS) -o $@ $<
endif

.PHONY: clean 
clean: 
	$(RM) -rf lib.a lib.x86.a
	$(RM) -rf *.o
	$(RM) -rf ./arch/*/*.o
