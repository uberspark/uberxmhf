# top-level makefile for runtime
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = runtimesup.S 
C_SOURCES = runtime.c globals.c libemhf.c 

AS_SOURCES += islayersup_svm.S 
C_SOURCES += islayer_svm.c apic_svm.c  

AS_SOURCES += islayersup_vmx.S  
C_SOURCES += apic_vmx.c islayer_vmx.c islayer_vmx_ug.c  


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))


OBJECTS_PRECOMPILED = ../libcommon/mpsup.o ../libcommon/string.o ../libcommon/delay_pit.o ../libcommon/txt_mtrrs.o ../libcommon/pci.o ../libcommon/acpi.o  ../libcommon/svm_eap.o ../libcommon/vmx_eap.o

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../libcommon/dbg_printf.o ../libcommon/dbg_vgamem.o
endif

OBJECTS_PRECOMPILED += $(wildcard $(APPOBJECTSDIR)/*.o) 

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: runtime.bin

runtime.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) runtime.lds.S
	$(LD) -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
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


