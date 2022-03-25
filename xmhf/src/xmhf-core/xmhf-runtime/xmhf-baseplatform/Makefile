# makefile for xmhf-baseplatform (EMHF base platform component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/x86/bplt-x86-$(TARGET_SUBARCH)-smptrampoline.S
AS_SOURCES +=  ./arch/x86/bplt-x86-$(TARGET_SUBARCH)-smplock.S

C_SOURCES = bplt-interface.c bplt-interface-runtime.c 
C_SOURCES += bplt-interface-smp.c
C_SOURCES += bplt-data.c

C_SOURCES += ./arch/x86/bplt-x86.c
C_SOURCES += ./arch/x86/bplt-x86-data.c
C_SOURCES += ./arch/x86/bplt-x86-pci.c
C_SOURCES += ./arch/x86/bplt-x86-acpi.c
C_SOURCES += ./arch/x86/bplt-x86-pit.c
C_SOURCES += ./arch/x86/bplt-x86-smp.c
C_SOURCES += ./arch/x86/bplt-x86-addressing.c
C_SOURCES += ./arch/x86/bplt-x86-reboot.c
C_SOURCES += ./arch/x86/bplt-x86-cpu.c


C_SOURCES += ./arch/x86/vmx/bplt-x86vmx.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-data.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-vmcs.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-smp.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-mtrrs.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-reboot.c


C_SOURCES += ./arch/x86/svm/bplt-x86svm.c
C_SOURCES += ./arch/x86/svm/bplt-x86svm-data.c
C_SOURCES += ./arch/x86/svm/bplt-x86svm-smp.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_SUBARCH), amd64)
AS_SOURCES32 =  ./arch/x86/bplt-x86-i386-smplock.S
C_SOURCES32 =  ./arch/x86/bplt-x86-pci.c
C_SOURCES32 += ./arch/x86/bplt-x86-acpi.c
C_SOURCES32 += ./arch/x86/bplt-x86-addressing.c
C_SOURCES32 += ./arch/x86/bplt-x86-cpu.c
C_SOURCES32 += ./arch/x86/vmx/bplt-x86vmx-mtrrs.c

AS_OBJECTS32 = $(patsubst %.S, %.x86.o, $(AS_SOURCES32))
C_OBJECTS32 = $(patsubst %.c, %.x86.o, $(C_SOURCES32))
OBJECTS += $(AS_OBJECTS32)
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
ifeq ($(TARGET_SUBARCH), amd64)
$(AS_OBJECTS32): %.x86.o: %.S $(I_SOURCES) Makefile ../Makefile ../../Makefile
	$(CC32) -c $(BCFLAGS) -o $@ $<
$(C_OBJECTS32): %.x86.o: %.c $(I_SOURCES) Makefile ../Makefile ../../Makefile
	$(CC32) -c $(BCFLAGS) -o $@ $<
endif

.PHONY: clean
clean:
	$(RM) -rf *.o
	$(RM) -rf ./arch/*/*.o
	$(RM) -rf ./arch/*/svm/*.o
	$(RM) -rf ./arch/*/vmx/*.o

