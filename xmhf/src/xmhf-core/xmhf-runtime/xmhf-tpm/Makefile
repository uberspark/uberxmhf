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

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_SUBARCH), amd64)
C_SOURCES32 =  ./tpm-interface.c
C_SOURCES32 += ./arch/x86/tpm-x86.c
C_SOURCES32 += ./arch/x86/svm/tpm-x86svm.c
C_SOURCES32 += ./arch/x86/vmx/tpm-x86vmx.c

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
	$(RM) -rf ./arch/x86/*.o
	$(RM) -rf ./arch/x86/svm/*.o
	$(RM) -rf ./arch/x86/vmx/*.o
