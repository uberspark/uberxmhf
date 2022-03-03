# makefile for xmhf-baseplatform (EMHF base platform component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smptrampoline.S
AS_SOURCES +=  ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smplock.S

C_SOURCES = bplt-interface.c
C_SOURCES += bplt-interface-smp.c
C_SOURCES += bplt-data.c

C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM).c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-data.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-pci.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-acpi.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-pit.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-smp.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-addressing.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-reboot.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/bplt-$(TARGET_HWPLATFORM)-cpu.c


C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-data.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-vmcs.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-smp.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-mtrrs.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-reboot.c


C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm-data.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm-smp.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_HWPLATFORM), x86_64)
AS_SOURCES32 =  ./arch/x86/bplt-x86-smplock.S
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
	# Optional: use sparse file to reduce fs space usage
	fallocate -d ./arch/$(TARGET_HWPLATFORM)/vmx/bplt-$(TARGET_HWPLATFORM)vmx-data.o
	fallocate -d ./arch/$(TARGET_HWPLATFORM)/svm/bplt-$(TARGET_HWPLATFORM)svm-data.o

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_HWPLATFORM), x86_64)
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

