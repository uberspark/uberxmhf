# makefile for xmhf-partition (EMHF component for handling partition
# setup and instantiation)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/x86/vmx/part-x86vmx-sup.S
AS_SOURCES +=  ./arch/x86/svm/part-x86svm-sup.S


C_SOURCES = part-interface.c

C_SOURCES += ./arch/x86/part-x86.c
C_SOURCES += ./arch/x86/vmx/part-x86vmx.c
C_SOURCES += ./arch/x86/svm/part-x86svm.c


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
 
  
  

  
