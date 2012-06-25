# makefile for xmhf-baseplatform (EMHF base platform component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/x86/bplt-x86-smptrampoline.S
AS_SOURCES +=  ./arch/x86/bplt-x86-smplock.S

C_SOURCES = bplt-interface.c
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
	
 
  
  

  
