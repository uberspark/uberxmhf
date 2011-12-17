# top-level makefile for runtime
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = runtimesup.S 
C_SOURCES = runtime.c globals.c libemhf.c 

AS_SOURCES += islayersup_svm.S 
C_SOURCES += islayer_svm.c apic_svm.c  

AS_SOURCES += islayersup_vmx.S  
C_SOURCES += apic_vmx.c islayer_vmx.c islayer_vmx_ug.c  

# These are the core runtime objects
OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

### Bring in libcommon/*.o so that App's (e.g., TrustVisor) can use them
# WARNING: if both Serial & VGA are enabled, you actually get neither. 
# TODO: Fix it.
ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += $(filter-out %dbg_vgamem.o,$(wildcard ../libcommon/*.o))
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += $(filter-out %dbg_uart.o,$(wildcard ../libcommon/*.o))
endif

# tie components used by the runtime
OBJECTS_PRECOMPILED += ../components/emhf-memprot/emhf-memprot.o
OBJECTS_PRECOMPILED += ../components/emhf-memprot/arch/vmx/emhf-memprot-vmx.o
OBJECTS_PRECOMPILED += ../components/emhf-memprot/arch/svm/emhf-memprot-svm.o

OBJECTS_PRECOMPILED += ../components/emhf-parteventhub/arch/x86/svm/peh-x86svm-entry.o
OBJECTS_PRECOMPILED += ../components/emhf-parteventhub/arch/x86/svm/peh-x86svm-main.o
OBJECTS_PRECOMPILED += ../components/emhf-parteventhub/arch/x86/vmx/peh-x86vmx-entry.o
OBJECTS_PRECOMPILED += ../components/emhf-parteventhub/arch/x86/vmx/peh-x86vmx-main.o

OBJECTS_PRECOMPILED += ../components/emhf-smpguest/smpg-interface.o
OBJECTS_PRECOMPILED += ../components/emhf-smpguest/arch/x86/svm/smpg-x86svm.o
OBJECTS_PRECOMPILED += ../components/emhf-smpguest/arch/x86/vmx/smpg-x86vmx.o

OBJECTS_PRECOMPILED += ../components/emhf-dmaprot/dmap-interface.o
OBJECTS_PRECOMPILED += ../components/emhf-dmaprot/arch/x86/svm/dmap-x86svm.o


I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: runtime.bin

runtime.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) runtime.lds.S
	$(LD) -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(ADDL_LIBS)
	$(OBJCOPY) --output-format=binary runtime.exe runtime.bin

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile 
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz


