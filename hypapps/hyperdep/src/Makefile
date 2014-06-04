#-------------------------------------------------------------------------------
# makefile for XMHF apps
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 
C_SOURCES = appmain.c
I_SOURCES =  $(wildcard ./*.h)

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

CFLAGS += -I.

# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.c   
	@echo Building "$(@F)" from "$<" 
	$(CC) -S -emit-llvm $(CFLAGS) $< -o $(@F).ll
	llc -O=0 $(@F).ll
	$(CC) -c $(CFLAGS) $(@F).s -o $(@F)

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.s
	$(RM) -rf *.ll
	
