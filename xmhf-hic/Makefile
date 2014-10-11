########################################################################
#
# Makefile for XMHF HIC
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.lscript $(srcdir)

#export PKG_CONFIG ?= pkg-config
#export XMHF_PKG_CONFIG_MODNAME=xmhf
#XMHF_DIR=$(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_dir)


########################################################################

export XMHF_HIC_NAME := xmhf-hic
export XMHF_HIC_SOURCES := $(wildcard $(srcdir)/*.c)
XMHF_HIC_SOURCES += $(shell find $(srcdir)/arch/$(XMHF_TARGET_TRIAD)/ -type f -name '*.c')


########################################################################
# generic build harness

XMHF_HIC_SOURCES_SUBST := $(patsubst $(srcdir)/%, %, $(XMHF_HIC_SOURCES))

# grab list of file names only for binary generation
XMHF_HIC_SOURCES_FILENAMEONLY := $(notdir $(XMHF_HIC_SOURCES_SUBST))

XMHF_HIC_OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(XMHF_HIC_SOURCES_FILENAMEONLY))
#XMHF_HIC_OBJECTS_ARCHIVE := $(patsubst %.S, %.o, $(XMHF_HIC_OBJECTS_ARCHIVE))

# list of object dependencies
XMHF_HIC_OBJECTS := $(patsubst %.c, %.o, $(XMHF_HIC_SOURCES_SUBST))
#XMHF_HIC_OBJECTS := $(patsubst %.S, %.o, $(XMHF_HIC_OBJECTS))

# folder where objects go
XMHF_HIC_OBJECTS_DIR := _objs_$(XMHF_HIC_NAME)

LINKER_SCRIPT_INPUT := $(XMHF_DIR)/xmhf-hic/xmhf-hic.lscript
LINKER_SCRIPT_OUTPUT := $(XMHF_HIC_NAME).lds


# LLC flags
LLC_ATTR = -3dnow,-3dnowa,+64bit,+64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop

# targets
.PHONY: all
all: buildhicbin

buildhicbin: $(XMHF_HIC_OBJECTS)
	cd $(XMHF_HIC_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) $(XMHF_HIC_NAME).lscript.c
	cd $(XMHF_HIC_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E $(XMHF_HIC_NAME).lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(XMHF_HIC_OBJECTS_DIR) && $(LD) -r --oformat elf64-x86-64 -T $(LINKER_SCRIPT_OUTPUT) -o $(XMHF_HIC_NAME).slo $(XMHF_HIC_OBJECTS_ARCHIVE) -L$(CCLIB)/lib/linux -L$(XMHFLIBS_DIR) -lxmhfc -lxmhfcrypto -lxmhfutil -lxmhfhw -lxmhfutil -lxmhfc -lclang_rt.builtins-x86_64
	cd $(XMHF_HIC_OBJECTS_DIR) && nm $(XMHF_HIC_NAME).slo | awk '{ print $$3 }' | awk NF >$(XMHF_HIC_NAME).slo.syms
	cd $(XMHF_HIC_OBJECTS_DIR) && $(OBJCOPY) --localize-symbols=$(XMHF_HIC_NAME).slo.syms $(XMHF_HIC_NAME).slo $(XMHF_HIC_NAME).slo
	cd $(XMHF_HIC_OBJECTS_DIR) && $(OBJCOPY) --globalize-symbol libxmhfdebug_lock --globalize-symbol xcbootinfo $(XMHF_HIC_NAME).slo $(XMHF_HIC_NAME).slo

%.o: %.c
	mkdir -p $(XMHF_HIC_OBJECTS_DIR)
	$(CC) -fomit-frame-pointer -O2 -S -emit-llvm $(CFLAGS) $< -o $(XMHF_HIC_OBJECTS_DIR)/$(@F).ll
	cd $(XMHF_HIC_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	cd $(XMHF_HIC_OBJECTS_DIR) && llc -O=2 -march=x86-64 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(XMHF_HIC_OBJECTS_DIR) && $(CC) -c $(CFLAGS) $(@F).s -o $(@F)

#%.o: %.S
#	mkdir -p $(XMHF_HIC_OBJECTS_DIR)
#	cd $(XMHF_HIC_OBJECTS_DIR) && gcc -c $(CFLAGS) $< -o $(@F)


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_HIC_OBJECTS_DIR)




