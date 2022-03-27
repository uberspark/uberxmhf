# makefile for EMHF debug component
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
AS_SOURCES_BL =

C_SOURCES = dbg-interface.c 
C_SOURCES += ./arch/x86/emhf_debug_arch.c

ifeq ($(DEBUG_SERIAL), y)
C_SOURCES += ./arch/x86/dbg-x86-uart.c
endif

ifeq ($(DEBUG_VGA), y)
C_SOURCES += ./arch/x86/dbg-x86-vgamem.c
endif

C_SOURCES_BL = $(C_SOURCES)

EXTRA_CLEAN = lib.a lib.x86.a

# targets
include ../runtime.mk

all: lib.a

lib.a: $(OBJECTS)
	$(AR) rvs $@ $^

# TODO: Workaround to compile x86 for bootloader
ifeq ($(TARGET_SUBARCH), amd64)
all: lib.x86.a

lib.x86.a: $(OBJECTS_BL)
	$(AR) rvs $@ $^
endif

