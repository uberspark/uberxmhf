# makefile for xmhf-xcphandler (EMHF exception handler component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = ./arch/x86/xcph-stubs.S 
C_SOURCES = xcph-interface.c

C_SOURCES += ./arch/x86/xcph-x86.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf ./arch/x86/*.o
 
  
  

  
