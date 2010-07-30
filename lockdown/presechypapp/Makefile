################################################################################
# intel vt vmm with v86 monitor
# author: amit vasudevan (amitvasudevan@acm.org)
#
# top level makefile
#
# history:
# 10/2/2009 12:10:51 PM  - initial version

# configuration options
export TARGET = intel-vt-v86vmm
export TARGET_VERSION = 0
export TARGET_SUBVERSION = 1
export BASEDIR = $(CURDIR)
export BUILDDIR = target_build
export INCLUDEDIR = $(BASEDIR)/include
# export INSTALLDIR = /cygdrive/Z
export INSTALLDIR = ./build

export DEBUG_SERIAL := y
export DEBUG_VGA	:= n

# hypervisor configuration
export CONF_SKELETON_ISLAYER := y
export CONF_HARDWARE_PAGING := n

export CONF_SHADOW_PAGING := n
export CONF_SHADOW_PAGING_NPAE := n
export CONF_SHADOW_PAGING_PAE := n
export CONF_SHADOW_PAGING_NPAE_ALG0 := n



# guest OS configuration
export CONF_GUESTOS_LINUX := n

# tools
export TOOLSBASE = $(CURDIR)/../../tools/bin
export CC = $(TOOLSBASE)/gcc
export O_CC = /bin/gcc
export RM = rm 
export CP = cp
export AS = $(TOOLSBASE)/as
export LD = $(TOOLSBASE)/ld
export O_LD = /bin/ld
export TAR = tar
export OBJDUMP = $(TOOLSBASE)/objdump
export OBJCOPY = $(TOOLSBASE)/objcopy
export SED = sed
export STRIP = $(TOOLSBASE)/strip

# basic flags for compiling
# -Wconversion
CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
CFLAGS += -fno-stack-protector
# CFLAGS += -Wall -Wstrict-prototypes -Wdeclaration-after-statement -Werror 
CFLAGS += -Wno-pointer-arith -Wextra -Wfloat-equal 
CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare
CFLAGS += -Waggregate-return
CFLAGS += -Wunreachable-code -Winline 
CFLAGS += -m32 -mtune=generic 
CFLAGS += -nostdinc -pipe -I$(INCLUDEDIR)

ifeq ($(DEBUG_SERIAL), y)
CFLAGS += -D__DEBUG_SERIAL__
endif
ifeq ($(DEBUG_VGA), y)
CFLAGS += -D__DEBUG_VGA__
endif

ifeq ($(CONF_SKELETON_ISLAYER), y)
CFLAGS += -D__CONF_SKELETON_ISLAYER__
endif

ifeq ($(CONF_HARDWARE_PAGING), y)
CFLAGS += -D__CONF_HARDWARE_PAGING__
endif
ifeq ($(CONF_SHADOW_PAGING), y)
CFLAGS += -D__CONF_SHADOW_PAGING__
endif

ifeq ($(CONF_SHADOW_PAGING_NPAE), y)
CFLAGS += -D__CONF_SHADOW_PAGING_NPAE__
endif
ifeq ($(CONF_SHADOW_PAGING_NPAE_ALG0), y)
CFLAGS += -D__CONF_SHADOW_PAGING_NPAE_ALG0__
endif
ifeq ($(CONF_SHADOW_PAGING_PAE), y)
CFLAGS += -D__CONF_SHADOW_PAGING_PAE__
endif


ifeq ($(CONF_GUESTOS_LINUX), y)
CFLAGS += -D__CONF_GUESTOS_LINUX__
endif


ASFLAGS = $(CFLAGS) -D__ASSEMBLY__

export CFLAGS
export ASFLAGS

# source directories
export SOURCEDIRS = 

# rules for building the subdirectories
.PHONY: all
all: 

	#make common and debug components first	
	cd common && $(MAKE) -w all
	cd debug && $(MAKE) -w all

	#make loader
	cd loader	&& $(MAKE) -w all

	#make runtime
	cd runtime	&& $(MAKE) -w all
	cd runtime  && gzip -c runtime.bin > runtime.bin.gz

	#copy relevant binaries to appropriate locations
	$(CP) loader/loader.bin $(INSTALLDIR)/loader.bin
	$(CP) runtime/runtime.bin.gz $(INSTALLDIR)/runtime.bin.gz
	
# cleanup rules
.PHONY: clean 
clean: 
	cd common && $(MAKE) -w clean
	cd debug && $(MAKE) -w clean
	cd loader && $(MAKE) -w clean
	cd runtime && $(MAKE) -w clean

   
# install rules


