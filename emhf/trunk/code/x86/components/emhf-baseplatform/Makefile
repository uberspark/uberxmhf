# makefile for emhf-baseplatform (EMHF base platform component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  ./arch/x86/bplt-x86-smptrampoline.S
AS_SOURCES +=  ./arch/x86/bplt-x86-smplock.S

C_SOURCES = bplt-interface.c
C_SOURCES += bplt-interface-smp.c

C_SOURCES += ./arch/x86/bplt-x86.c
C_SOURCES += ./arch/x86/bplt-x86-pci.c
C_SOURCES += ./arch/x86/bplt-x86-acpi.c
C_SOURCES += ./arch/x86/bplt-x86-pit.c
C_SOURCES += ./arch/x86/bplt-x86-smp.c

C_SOURCES += ./arch/x86/vmx/bplt-x86vmx.c
C_SOURCES += ./arch/x86/vmx/bplt-x86vmx-mtrrs.c


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
 
  
  

  
