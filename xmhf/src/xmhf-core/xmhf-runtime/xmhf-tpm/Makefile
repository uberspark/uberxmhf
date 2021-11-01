# makefile for EMHF TPM component
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 
C_SOURCES = tpm-interface.c  

C_SOURCES += ./arch/x86/tpm-x86.c
C_SOURCES += ./arch/x86/svm/tpm-x86svm.c
C_SOURCES += ./arch/x86/vmx/tpm-x86vmx.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

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
	$(RM) -rf ./arch/x86/svm/*.o
	$(RM) -rf ./arch/x86/vmx/*.o
