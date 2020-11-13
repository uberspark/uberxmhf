# common Makefile boilerplate for XMHF
# author: amit vasudevan (amitvasudevan@acm.org)

mydir := $(dir $(lastword $(MAKEFILE_LIST)))
mydir := $(realpath $(mydir))




######
# autoconf controlled variables
######

export MAKE = make
export UBERSPARKCONFIG = ubersparkconfig
export FRAMAC = frama-c
export CCERT = ccomp
export CC = gcc -m32
export AS = as
export AR = ar
export RM = rm -f
export CP = cp				
export MKDIR = mkdir
export LD = ld
export OBJCOPY = objcopy
export CAT = cat
#export CCLIB = @CCLIB@
#export CCLIB := $(realpath $(CCLIB))

export prefix=/usr/local

export DEBUG_SERIAL := y
export DEBUG_SERIAL_PORT := 0x3f8
export XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS	:= 4

#export DEBUG_VGA := @DEBUG_VGA@
export DRT := y
export DMAP := y
export XMHF_TARGET_CPU := x86
export XMHF_TARGET_CONTAINER := vmx
export XMHF_TARGET_PLATFORM := x86pc



######
# pull-in base uberspark common makefile
######

UBERSPARK_HOMEDIR := $(shell $(UBERSPARKCONFIG) --print-uberspark-homedir)
include $(UBERSPARK_HOMEDIR)/uberspark-common.mk




######
# uxmhf common variables
######

export XMHF_TARGET_TRIAD := $(XMHF_TARGET_CPU)-$(XMHF_TARGET_CONTAINER)-$(XMHF_TARGET_PLATFORM)
CCERT_REALPATH := $(realpath $(shell which $(CCERT)))
CCERT_BINDIR := $(dir $(CCERT_REALPATH))
CCERT_BINDIR_NOSLASH := $(CCERT_BINDIR:/=)
export CCERT_LIB :=  $(dir $(CCERT_BINDIR_NOSLASH))lib/compcert/

######
# configuration definitions
######

export XMHFGEEC_TOTAL_UHSLABS := 1
export XMHFGEEC_TOTAL_UGSLABS := 1

## load base, at 36M
export XMHF_CONFIG_LOADADDR := 0x06200000
## load max size
export XMHF_CONFIG_LOADMAXSIZE := 0x1D200000
## load max addr
export XMHF_CONFIG_LOADMAXADDR := 0x23400000
## system max addr, 4GB
export XMHF_CONFIG_MAXSYSADDR := 0xFFFFFFFF

export XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES := 6
export XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES := 6

export XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES := 64


## build version
#export XMHF_BUILD_VERSION := $(shell git describe --abbrev=0)
export XMHF_BUILD_VERSION := 4.1

## build revision
#export XMHF_BUILD_REVISION_BRANCH := $(shell git rev-parse --abbrev-ref HEAD)
#export XMHF_BUILD_REVISION_COMMIT := $(shell git log --pretty=format:'%H' -n 1)
#export XMHF_BUILD_REVISION := $(XMHF_BUILD_REVISION_BRANCH)-$(XMHF_BUILD_REVISION_COMMIT)
export XMHF_BUILD_REVISION := sometimes-even-the-wisest-of-man-and-machines-can-be-in-error







######
# common paths
######

## directory where this Makefile resides (source root)
export XMHF_DIR := $(mydir)

## objects directory (used for building binaries without polluting source namespace)
export XMHF_OBJDIR = $(XMHF_DIR)/_objects

## XMHF libs dirs and object locations
export XMHF_LIBDIRS := $(wildcard $(XMHF_DIR)/libs/lib*)
export XMHF_LIBS_OBJECTS_DIR := $(XMHF_OBJDIR)/_objs_libs

# construct XMHF additional include paths for verification and build
XMHF_ADDL_INCLUDES := 
XMHF_V_ADDL_INCLUDES :=
XMHF_ADDL_INCLUDES += -I$(XMHF_DIR)/include
XMHF_V_ADDL_INCLUDES += -cpp-extra-args=-I$(XMHF_DIR)/include
XMHF_ADDL_INCLUDES += -I$(XMHF_DIR)/xmhf-uobjs/include 
XMHF_V_ADDL_INCLUDES += -cpp-extra-args=-I$(XMHF_DIR)/xmhf-uobjs/include 
XMHF_LIBSINC = $(foreach dir,$(XMHF_LIBDIRS),-I$(dir)/include)
XMHF_V_LIBSINC = $(foreach dir,$(XMHF_LIBDIRS),-cpp-extra-args=-I$(dir)/include)
XMHF_ADDL_INCLUDES += $(XMHF_LIBSINC)
XMHF_V_ADDL_INCLUDES += $(XMHF_V_LIBSINC)

# construct module list that comprise the hardware model
UBERSPARK_HWMDIR := $(shell $(UBERSPARKCONFIG) --print-uberspark-hwmdir)
export V_XMHFHWM_MODULES := $(realpath $(wildcard $(UBERSPARK_HWMDIR)/*.c))

# construct module list that comprise libubersparkhw
UBERSPARK_LIBSDIR := $(shell $(UBERSPARKCONFIG) --print-uberspark-libsdir)
V_LIBXMHFHW_MODULES_DIR := $(realpath $(UBERSPARK_LIBSDIR)/libubersparkhw)
V_LIBXMHFHW_MODULES_ABS := $(wildcard $(V_LIBXMHFHW_MODULES_DIR)/*.c)
V_LIBXMHFHW_MODULES_ABS += $(wildcard $(V_LIBXMHFHW_MODULES_DIR)/*.cS)
V_LIBXMHFHW_MODULES := $(patsubst $(V_LIBXMHFHW_MODULES_DIR)/%, %, $(V_LIBXMHFHW_MODULES_ABS))
export V_LIBXMHFHW_MODULES_DIR;
export V_LIBXMHFHW_MODULES;

# construct directory for libxmhfgeec
V_LIBXMHFGEEC_MODULES_DIR := $(realpath $(UBERSPARK_LIBSDIR)/libxmhfgeec)
export V_LIBXMHFGEEC_MODULES_DIR;



















######
# compiler/assembler flags
######

## three flags, CCERT_FLAGS, V_FLAGS and ASMFLAGS are brought in by uberspark
## current XMHF build process expects verification flags in VFLAGS

ASMFLAGS += $(XMHF_ADDL_INCLUDES)
CCERT_FLAGS += $(XMHF_ADDL_INCLUDES)
V_FLAGS += $(XMHF_V_ADDL_INCLUDES)

ASMFLAGS += -D___XMHF_BUILD_VERSION___=\"$(XMHF_BUILD_VERSION)\"
CCERT_FLAGS += -D___XMHF_BUILD_VERSION___=\"$(XMHF_BUILD_VERSION)\"
V_FLAGS += -cpp-extra-args=-D___XMHF_BUILD_VERSION___=\"$(XMHF_BUILD_VERSION)\"

ASMFLAGS += -D___XMHF_BUILD_REVISION___=\"$(XMHF_BUILD_REVISION)\"
CCERT_FLAGS += -D___XMHF_BUILD_REVISION___=\"$(XMHF_BUILD_REVISION)\"
V_FLAGS += -cpp-extra-args=-D___XMHF_BUILD_REVISION___=\"$(XMHF_BUILD_REVISION)\"

# target cpu
ifeq ($(XMHF_TARGET_CPU), x86)
	ASMFLAGS += -D__XMHF_TARGET_CPU_X86__
	CCERT_FLAGS += -D__XMHF_TARGET_CPU_X86__
	V_FLAGS += -cpp-extra-args=-D__XMHF_TARGET_CPU_X86__
endif

# target container
ifeq ($(XMHF_TARGET_CONTAINER), vmx)
	ASMFLAGS += -D__XMHF_TARGET_CONTAINER_VMX__
	CCERT_FLAGS += -D__XMHF_TARGET_CONTAINER_VMX__
	V_FLAGS += -cpp-extra-args=-D__XMHF_TARGET_CONTAINER_VMX__
endif

# target platform
ifeq ($(XMHF_TARGET_PLATFORM), x86pc)
	ASMFLAGS += -D__XMHF_TARGET_PLATFORM_X86PC__
	CCERT_FLAGS += -D__XMHF_TARGET_PLATFORM_X86PC__
	V_FLAGS += -cpp-extra-args=-D__XMHF_TARGET_PLATFORM_X86PC__
endif

# target triad
ifeq ($(XMHF_TARGET_TRIAD), x86-vmx-x86pc)
	ASMFLAGS += -D__XMHF_TARGET_TRIAD_X86_VMX_X86PC__
	CCERT_FLAGS += -D__XMHF_TARGET_TRIAD_X86_VMX_X86PC__
	V_FLAGS += -cpp-extra-args=-D__XMHF_TARGET_TRIAD_X86_VMX_X86PC__
endif

# other options
ifeq ($(DEBUG_SERIAL), y)
	ASMFLAGS += -D__DEBUG_SERIAL__
	CCERT_FLAGS += -D__DEBUG_SERIAL__
	V_FLAGS += -cpp-extra-args=-D__DEBUG_SERIAL__

	ASMFLAGS += -D__DEBUG_SERIAL__
	CCERT_FLAGS += -DDEBUG_PORT=$(DEBUG_SERIAL_PORT)
	V_FLAGS += -cpp-extra-args=-DDEBUG_PORT=$(DEBUG_SERIAL_PORT)

	ASMFLAGS += -D__DEBUG_SERIAL__
	CCERT_FLAGS += -D__XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS__=$(XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS)
	V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS__=$(XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS)
endif
ifeq ($(DRT), y)
	ASMFLAGS += -D__DRT__
	CCERT_FLAGS += -D__DRT__
	V_FLAGS += -cpp-extra-args=-D__DRT__
endif
ifeq ($(DMAP), y)
	ASMFLAGS += -D__DMAP__
	CCERT_FLAGS += -D__DMAP__
	V_FLAGS += -cpp-extra-args=-D__DMAP__
endif


# configuration definitions
ASMFLAGS += -D__XMHFGEEC_TOTAL_UHSLABS__=$(XMHFGEEC_TOTAL_UHSLABS)
CCERT_FLAGS += -D__XMHFGEEC_TOTAL_UHSLABS__=$(XMHFGEEC_TOTAL_UHSLABS)
V_FLAGS += -cpp-extra-args=-D__XMHFGEEC_TOTAL_UHSLABS__=$(XMHFGEEC_TOTAL_UHSLABS)

ASMFLAGS += -D__XMHFGEEC_TOTAL_UGSLABS__=$(XMHFGEEC_TOTAL_UGSLABS)
CCERT_FLAGS += -D__XMHFGEEC_TOTAL_UGSLABS__=$(XMHFGEEC_TOTAL_UGSLABS)
V_FLAGS += -cpp-extra-args=-D__XMHFGEEC_TOTAL_UGSLABS__=$(XMHFGEEC_TOTAL_UGSLABS)

ASMFLAGS += -D__XMHF_CONFIG_LOADADDR__=$(XMHF_CONFIG_LOADADDR)
CCERT_FLAGS += -D__XMHF_CONFIG_LOADADDR__=$(XMHF_CONFIG_LOADADDR)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_LOADADDR__=$(XMHF_CONFIG_LOADADDR)

ASMFLAGS += -D__XMHF_CONFIG_LOADMAXSIZE__=$(XMHF_CONFIG_LOADMAXSIZE)
CCERT_FLAGS += -D__XMHF_CONFIG_LOADMAXSIZE__=$(XMHF_CONFIG_LOADMAXSIZE)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_LOADMAXSIZE__=$(XMHF_CONFIG_LOADMAXSIZE)

ASMFLAGS += -D__XMHF_CONFIG_LOADMAXADDR__=$(XMHF_CONFIG_LOADMAXADDR)
CCERT_FLAGS += -D__XMHF_CONFIG_LOADMAXADDR__=$(XMHF_CONFIG_LOADMAXADDR)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_LOADMAXADDR__=$(XMHF_CONFIG_LOADMAXADDR)

ASMFLAGS += -D__XMHF_CONFIG_MAXSYSADDR__=$(XMHF_CONFIG_MAXSYSADDR)
CCERT_FLAGS += -D__XMHF_CONFIG_MAXSYSADDR__=$(XMHF_CONFIG_MAXSYSADDR)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_MAXSYSADDR__=$(XMHF_CONFIG_MAXSYSADDR)

ASMFLAGS += -D__XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES__=$(XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES)
CCERT_FLAGS += -D__XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES__=$(XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES__=$(XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES)

ASMFLAGS += -D__XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES__=$(XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES)
CCERT_FLAGS += -D__XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES__=$(XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES__=$(XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES)

ASMFLAGS += -D__XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES__=$(XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES)
CCERT_FLAGS += -D__XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES__=$(XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES)
V_FLAGS += -cpp-extra-args=-D__XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES__=$(XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES)


export VFLAGS := $(V_FLAGS)





