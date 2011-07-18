# makefile for libcommon
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  mpsup.S
C_SOURCES = string.c dbg_printf.c dbg_vgamem.c delay_pit.c sha1.c hmac.c txt_mtrrs.c tpm.c tpm_extra.c tpm_emhf.c pci.c acpi.c svm_eap.c vmx_eap.c strtoul.c strncpy.c strlen.c strcmp.c

ifeq ($(DEBUG_SERIAL), y)
C_SOURCES += dbg_uart.c
endif

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
 
  
  

  
