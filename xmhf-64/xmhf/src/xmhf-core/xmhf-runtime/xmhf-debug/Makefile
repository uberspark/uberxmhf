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

ifeq ($(DEBUG_EVENT_LOGGER), y)
C_SOURCES += dbg-event-logger.c
endif

C_SOURCES_BL = $(C_SOURCES)

EXTRA_CLEAN = lib.a lib.i386.a

# targets
include ../runtime.mk

all: lib.a

lib.a: $(OBJECTS)
	$(AR) rvs $@ $^

# If runtime is amd64, compile i386 version of this library for bootloader
ifeq ($(TARGET_SUBARCH), amd64)
all: lib.i386.a

lib.i386.a: $(OBJECTS_BL)
	$(AR) rvs $@ $^
endif

