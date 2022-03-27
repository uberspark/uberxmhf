# makefile for xmhf-xmhfcbackend (libxmhfc backend component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  
C_SOURCES = xmhfc-putchar.c

C_SOURCES += ./stl/xmhfc-bitmap.c
C_SOURCES += ./stl/xmhfc-dlist.c

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_SUBARCH), amd64)
C_SOURCES32 =  ./xmhfc-putchar.c

C_OBJECTS32 = $(patsubst %.c, %.x86.o, $(C_SOURCES32))
OBJECTS += $(C_OBJECTS32)
endif

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_SUBARCH), amd64)
$(C_OBJECTS32): %.x86.o: %.c $(I_SOURCES) Makefile ../Makefile ../../Makefile
	$(CC32) -c $(BCFLAGS) -o $@ $<
endif

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf ./stl/*.o
