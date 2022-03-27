# makefile for xmhf-startup component
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
# AS_SOURCES = runtimesup.S
AS_SOURCES =

C_SOURCES = runtime.c
C_SOURCES += rntm-data.c

C_SOURCES += ./arch/x86/rntm-x86-data.c

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

.PHONY: clean
clean:
	$(RM) -rf *.o
	$(RM) -rf ./arch/x86/*.o

