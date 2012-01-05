# makefile for emhf-partition (EMHF component for handling partition
# setup and instantiation)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files

C_SOURCES = libemhf.c
C_SOURCES += applib-vmx.c
C_SOURCES += applib-svm.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# Awful, awful.  FIXME!
CFLAGS += -I../../../libemhfc/include/

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
 
  
  

  
