# makefile for emhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  
C_SOURCES = dmap-interface.c
C_SOURCES += ./arch/svm/dmap-x86svm.c


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
	$(RM) -rf ./arch/svm/*.o
 
  
  

  
