########################################################################
#
# common Makefile harness to build XMHF hypapps
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export PKG_CONFIG ?= pkg-config
export XMHF_PKG_CONFIG_MODNAME=xmhf

OBJCOPY ?= objcopy
LD ?= ld
export CC := clang

# grab XMHF data directory (where hypapp linker script is stored)
export XMHF_DATA_DIR := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_datadir)

# grab XMHF build configuration via pkg-config
# $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=)
export XMHF_TARGET_PLATFORM := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_buildconf_target_platform)
export XMHF_TARGET_ARCH := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_buildconf_target_arch)
export MP_VERSION := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_buildconf_mp_version)
export NESTED_PAGING := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_buildconf_nested_paging)
export CCLIB := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=cclibdir)
export XMHF_CORE_APIHUB_ARCH := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_buildconf_coreapihub_arch)
export XMHF_INCLUDEDIR := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_includedir)
export XMHF_LIBDIR := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_libdir)
export XMHF_CFLAGS := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --cflags)
export XMHF_LIBS := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --libs-only-l)
export XMHF_LIBS_DIR := $(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --libs-only-L)

# generate target platform/arch suffix
export TARGET_HWPLATFORM=x86

# generate linker script location
export XMHF_HYPAPP_LDS=$(XMHF_DATA_DIR)/xmhfhypapp.lds

# export default hypapp name (xmhfhypapp) -- can be overridden
export XMHF_HYPAPP_NAME=xmhfhypapp

# export default hypapp objs -- can be overridden
export XMHF_HYPAPP_OBJS=

# build FLAGS (compiler flags)
FLAGS = -O0 -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
FLAGS += -fno-stack-protector
FLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
FLAGS += -Wno-pointer-arith -Wextra -Wfloat-equal 
#FLAGS += -Werror
FLAGS += -Wsign-compare
FLAGS += -Wno-bad-function-cast -Wall
#FLAGS += -Waggregate-return
FLAGS += -Winline
FLAGS += -m32 -march=k8 
FLAGS += -mno-mmx -mno-sse -mno-sse2 -mno-sse3 -mno-ssse3 
FLAGS += -mno-sse4.1 -mno-sse4.2 -mno-sse4 -mno-avx -mno-aes 
FLAGS += -mno-pclmul -mno-sse4a -mno-sse5 -mno-3dnow -mno-popcnt -mno-abm
FLAGS += -nostdinc -pipe

# add XMHF FLAGS 
FLAGS += $(XMHF_CFLAGS)

# generate and add appropritate FLAGS for the build configuration options

ifeq ($(XMHF_TARGET_ARCH), x86-svm)
	FLAGS += -D__XMHF_TARGET_ARCH_X86_SVM__
endif
ifeq ($(XMHF_TARGET_ARCH), x86-vmx)
	FLAGS += -D__XMHF_TARGET_ARCH_X86_VMX__
endif
ifeq ($(XMHF_CORE_APIHUB_ARCH), swfp)
	FLAGS += -D__XMHF_CORE_APIHUB_SWFP__
endif
ifeq ($(NESTED_PAGING), y)
	FLAGS += -D__NESTED_PAGING__
endif
ifeq ($(MP_VERSION), y)
	FLAGS += -D__MP_VERSION__
endif

ASFLAGS = $(FLAGS) -D__ASSEMBLY__
export ASFLAGS

#CFLAGS = $(FLAGS) -no-integrated-as
CFLAGS = $(FLAGS) 
export CFLAGS


.PHONY: all
all: xmhfhypappall
	#$(LD) -T $(XMHF_HYPAPP_LDS) -o $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).exe $(XMHF_HYPAPP_OBJS) $(XMHF_LIBS_DIR) -lbaremetal $(XMHF_LIBS)
	$(LD) -T $(XMHF_HYPAPP_LDS) -o $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).exe $(XMHF_HYPAPP_OBJS) $(XMHF_LIBS_DIR) -lbaremetal $(XMHF_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	$(OBJCOPY) --output-format=binary $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).exe $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).bin
	gzip -c $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).bin > ./$(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).bin.gz
		

.PHONY: clean 
clean: xmhfhypappclean
	$(RM) -f $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).bin.gz
	rm -f $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).bin
	rm -f $(XMHF_HYPAPP_NAME)-$(TARGET_HWPLATFORM).exe
	
