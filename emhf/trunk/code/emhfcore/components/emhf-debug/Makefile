# makefile for EMHF debug component
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 

C_SOURCES = dbg-interface.c 

ifeq ($(DEBUG_SERIAL), y)
C_SOURCES += ./arch/x86/dbg-x86-uart.c
endif

ifeq ($(DEBUG_VGA), y)
C_SOURCES += ./arch/x86/dbg-x86-vgamem.c
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

%.o: %.S $(I_SOURCES) Makefile ../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf ./arch/x86/*.o
