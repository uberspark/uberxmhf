# Top-level makefile for TrustVisor
# Created by Arvind Seshadri 2/15/07
# This file is set up so that all object files and the final executable 
# are placed in a separate directory than the sources (variable B_DIR 
# below). This is done so that source directories can be NFS mounted 
# read-only on testing machines. This should eliminate any chances of
# source file corruption if the testing machine were to become unstable.

# Make variables
# Recursively expanded variables are expanded at time of substitution.
# They are defined using = 
# Simply expanded variables are expanded at the time of definition.
# They are defined using :=
# $@ is the name of the target.          
# $< is the first prerequisite of the target.
# $^ is the list of all prerequisites.

export BASEDIR=$(CURDIR)
# Build directory
export B_DIR = visor_out

# Debug option 
# Change this to ECM50, POSSUM, or GDB, depending on whether you are using
# ECM50, POSSUM, or SimNow/GDB for debugging
# Set this to n if you don't want debugging support
#DEBUG := POSSUM
DEBUG := n

# Config options 
export USE_SERIAL_OUTPUT := y

# Target name and version
export TARGET = TrustVisor
export SECVISOR_VERSION = 1
export SECVISOR_SUBVERSION = 0

#verbosity                                                                     
#ifeq ($(V), 1)                                                           
#export VERBOSE=@
#endif

# Tools
export CC = gcc
export RM = rm 
export AS = as
export LD = ld
export MKELF = $(BASEDIR)/$(B_DIR)/mkelf32
export TAR = tar
export NM = nm
export OBJDUMP = objdump
export OBJCOPY = objcopy
export SED = sed
export CHK_INIT = $(BASEDIR)/$(B_DIR)/chk_init

# Header files
export INCLUDE_DIR = $(BASEDIR)/include
INCLUDE = -I$(INCLUDE_DIR)

# Linker script
export LINKER_SCRIPT = $(BASEDIR)/$(B_DIR)/visor.lds

# Source files compilation indicator
export COMPILE_H = $(BASEDIR)/$(B_DIR)/compile.h

# Flags for compiling and linking
CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
#CFLAGS += -fno-stack-protector
CFLAGS += -Wall -Wstrict-prototypes -Wdeclaration-after-statement 
CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare 
#CFLAGS += -Wconversion
#CFLAGS += -Waggregate-return -Wmissing-field-initializers 
CFLAGS += -Waggregate-return
#CFLAGS += -Wunreachable-code
CFLAGS += -Winline
# -msoft-float: Generate output containing library calls for floating point.
# We need to provide libraries if we need FP.
CFLAGS += -m32 -march=k8 -msoft-float -mregparm=3
CFLAGS += -nostdinc -pipe $(INCLUDE)

ifeq ($(DEBUG), ECM50)
CFLAGS += -gdwarf-2 -D__DEBUG__ -O0
endif
ifeq ($(DEBUG), POSSUM)
CFLAGS += -g -D__DEBUG__ -O0
endif
ifeq ($(DEBUG), GDB)
CFLAGS += -g -D__DEBUG__ -D__SIM__ -O0
endif
ifeq ($(DEBUG), n)
CFLAGS += -g -D__DEBUG__ -O2
endif
ifeq ($(USE_SERIAL_OUTPUT), y)
CFLAGS += -D__USE_SERIAL__
endif

export CFLAGS
LDFLAGS = -T $(LINKER_SCRIPT)
ASFLAGS = $(CFLAGS) -D__ASSEMBLY__
export ASFLAGS

OBJCOPYFLAGS = -O binary -R .note -R .comment -S
export OBJCOPYFLAGS

# gcc flags for compiling mkelf32
HOSTCFLAGS = -Wall -Werror -Wstrict-prototypes -Wdeclaration-after-statement 
HOSTCFLAGS += -O2 -fomit-frame-pointer
export HOSTCFLAGS

# Source directories. If you add new source directories, add their
# names to this list. 
export S_DIRS = visor drivers tpm lib mm
S_DIRS_CLEAN = $(patsubst %, %_clean, $(S_DIRS))
S_DIRS_CLEAN += include_clean boot_clean
S_DIRS_CLEAN += loader_clean

# rules for building the subdirectories
.PHONY: $(S_DIRS) boot loader
boot:  $(S_DIRS) loader
	$(MAKE) -C $@ $(BASEDIR)/$(B_DIR)/$(TARGET)
	$(MAKE) -C hash visor
	$(MAKE) -C visor objs
	$(MAKE) -C $@ $(BASEDIR)/$(B_DIR)/$(TARGET).gz
$(S_DIRS): $(BASEDIR)/$(B_DIR)
	$(MAKE) -C $@ objs
loader: boot
	$(MAKE) -C $@ 
$(BASEDIR)/$(B_DIR):
	cd $(BASEDIR);\
	mkdir $(B_DIR)

# rules for make clean. 
.PHONY: clean $(S_DIRS_CLEAN)
clean: $(S_DIRS_CLEAN)
	$(RM) -rf $(B_DIR)
	$(RM) -f *~
	$(RM) -f TAGS
$(S_DIRS_CLEAN):
	$(MAKE) -C $(patsubst %_clean, %, $@) clean

install: 
	cp $(BASEDIR)/$(B_DIR)/TrustVisor.gz /boot
	cp $(BASEDIR)/loader/loader_out/TLoader.gz /boot

.PHONY: tags
tags:
	/usr/bin/ctags -e -R
