################################################################################
# intel vt vmm with v86 monitor
# author: amit vasudevan (amitvasudevan@acm.org)
#
# makefile for runtime
#
# history:
# 10/2/2009 12:27:52 PM  - initial version

# source files
AS_SOURCES = entry.S v86monitorsup.S islayersup.S
C_SOURCES = runtime.c  v86monitor.c  acpi.c

ifeq ($(CONF_SHADOW_PAGING), y)

	ifeq ($(CONF_SHADOW_PAGING_NPAE), y)
		C_SOURCES += islayer_shadowpaging.c shadow_paging_npae.c
	endif

	ifeq ($(CONF_SHADOW_PAGING_NPAE_ALG0), y)
		C_SOURCES += islayer_npae_alg0.c shadow_paging_npae_alg0.c
	endif

	ifeq ($(CONF_SHADOW_PAGING_PAE), y)
	
		C_SOURCES += islayer.c shadow_paging.c
	endif

endif

ifeq ($(CONF_HARDWARE_PAGING), y)
	
	ifeq ($(CONF_SHADOW_PAGING_NPAE), y)
		C_SOURCES += islayer_npae.c hardware_paging.c
	endif

	ifeq ($(CONF_SHADOW_PAGING_PAE), y)
		C_SOURCES += islayer.c hardware_paging.c
	endif

endif

ifeq ($(CONF_SKELETON_ISLAYER), y)
		C_SOURCES += islayer_skeleton.c 
endif


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_PRECOMPILED = $(wildcard ../common/*.o)

ifeq ($(DEBUG_SERIAL), y)
OBJECTS_PRECOMPILED += ../debug/printf.o ../debug/uart.o
endif
ifeq ($(DEBUG_VGA), y)
OBJECTS_PRECOMPILED += ../debug/printf.o ../debug/vgamem.o
endif

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS) 
	$(LD) --oformat=pe-i386 --image-base=0x80000000 -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED)
	$(CP) runtime.exe runtime_syms.exe
	$(STRIP) -s runtime.exe
	$(OBJCOPY) --input-format=pe-i386 --output-format=binary runtime.exe runtime.bin
	$(RM) -rf runtime.exe
	
%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<
    
.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	
  
