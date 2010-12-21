# top-level makefile for runtime
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = runtimesup.S 
C_SOURCES = runtime.c globals.c libsechyp.c 

AS_SOURCES += islayersup_svm.S 
C_SOURCES += islayer_svm.c apic_svm.c  

AS_SOURCES += islayersup_vmx.S  
C_SOURCES += apic_vmx.c islayer_vmx.c islayer_vmx_ug.c  


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))


OBJECTS_PRECOMPILED = ../libcommon/mpsup.o ../libcommon/string.o ../libcommon/delay_pit.o

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
all: $(OBJECTS) 
	$(LD) --oformat=pe-i386 --image-base=0xC0000000 -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
	$(CP) runtime.exe runtime_syms.exe
	$(STRIP) -s runtime.exe
	$(OBJCOPY) --input-format=pe-i386 --output-format=binary runtime.exe runtime.bin

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
	
  
