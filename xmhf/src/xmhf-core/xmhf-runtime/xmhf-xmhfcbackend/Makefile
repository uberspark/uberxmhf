# makefile for xmhf-xmhfcbackend (libxmhfc backend component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  
C_SOURCES = xmhfc-putchar.c

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_HWPLATFORM), x86_64)
C_SOURCES32 =  ./xmhfc-putchar.c

C_OBJECTS32 = $(patsubst %.c, %.x86.o, $(C_SOURCES32))
OBJECTS += $(C_OBJECTS32)
endif

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_HWPLATFORM), x86_64)
$(C_OBJECTS32): %.x86.o: %.c $(I_SOURCES) Makefile ../Makefile ../../Makefile
	$(CC32) -c $(BCFLAGS) -o $@ $<
endif

.PHONY: clean 
clean: 
	$(RM) -rf *.o

