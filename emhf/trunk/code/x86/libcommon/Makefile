# makefile for libcommon
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  mpsup.S
C_SOURCES = string.c dbg_printf.c dbg_uart.c dbg_vgamem.c delay_pit.c sha1.c txt_mtrrs.c tpm.c pci.c svm_eap.c

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
 
  
  

  
