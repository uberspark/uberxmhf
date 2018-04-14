# makefile for xmhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  
C_SOURCES = dmap-interface.c
C_SOURCES += ./arch/x86/dmap-x86.c
C_SOURCES += ./arch/x86/svm/dmap-x86svm.c

C_SOURCES += ./arch/x86/vmx/dmap-x86vmx.c
C_SOURCES += ./arch/x86/vmx/dmap-x86vmx-data.c


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
	$(RM) -rf ./arch/x86/svm/*.o
	$(RM) -rf ./arch/x86/vmx/*.o
 
  
  

  
