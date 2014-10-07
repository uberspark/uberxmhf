# common makefile for slabs
# author: amit vasudevan (amitvasudevan@acm.org)


XMHF_SLAB_SOURCES_SUBST := $(patsubst $(srcdir)/%, %, $(XMHF_SLAB_SOURCES))

# grab list of file names only for binary generation
XMHF_SLAB_SOURCES_FILENAMEONLY := $(notdir $(XMHF_SLAB_SOURCES_SUBST))

XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(XMHF_SLAB_SOURCES_FILENAMEONLY))
XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.S, %.o, $(XMHF_SLAB_OBJECTS_ARCHIVE))

# list of object dependencies
XMHF_SLAB_OBJECTS := $(patsubst %.c, %.o, $(XMHF_SLAB_SOURCES_SUBST))
XMHF_SLAB_OBJECTS := $(patsubst %.S, %.o, $(XMHF_SLAB_OBJECTS))

# folder where objects go
XMHF_SLAB_OBJECTS_DIR := _objs_slab_$(XMHF_SLAB_NAME)

LINKER_SCRIPT_INPUT := $(XMHF_DIR)/xmhfslab.lscript
LINKER_SCRIPT_OUTPUT := $(XMHF_SLAB_NAME).lds


# LLC flags
#LLC_ATTR = -3dnow,-3dnowa,-64bit,-64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop
LLC_ATTR = -3dnow,-3dnowa,+64bit,+64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop

# targets
.PHONY: all
all: buildslabbin

buildslabbin: $(XMHF_SLAB_OBJECTS)
	cd $(XMHF_SLAB_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) $(XMHF_SLAB_NAME).lscript.c
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E $(XMHF_SLAB_NAME).lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	#cd $(XMHF_SLAB_OBJECTS_DIR) && $(LD) -r --oformat elf64-x86-64 -T $(LINKER_SCRIPT_OUTPUT) -o $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_OBJECTS_ARCHIVE) -L$(CCLIB)/lib/linux -L$(XMHFLIBS_DIR) -lxmhfc -lxmhfcrypto -lxmhfutil -lxmhfhw -lxmhfutil -lxmhfc -lclang_rt.builtins-x86_64
	#cd $(XMHF_SLAB_OBJECTS_DIR) && nm $(XMHF_SLAB_NAME).slo | awk '{ print $$3 }' | awk NF >$(XMHF_SLAB_NAME).slo.syms
	#cd $(XMHF_SLAB_OBJECTS_DIR) && $(OBJCOPY) --localize-symbols=$(XMHF_SLAB_NAME).slo.syms $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_NAME).slo
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(LD) -r --oformat elf64-x86-64 -T $(LINKER_SCRIPT_OUTPUT) -o $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_OBJECTS_ARCHIVE) -L$(CCLIB)/lib/linux -L$(XMHFLIBS_DIR) -lxmhfc -lxmhfcrypto -lxmhfutil -lxmhfhw -lxmhfutil -lxmhfc -lclang_rt.builtins-x86_64
	cd $(XMHF_SLAB_OBJECTS_DIR) && nm $(XMHF_SLAB_NAME).slo | awk '{ print $$3 }' | awk NF >$(XMHF_SLAB_NAME).slo.syms
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(OBJCOPY) --localize-symbols=$(XMHF_SLAB_NAME).slo.syms $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_NAME).slo

%.o: %.c
	mkdir -p $(XMHF_SLAB_OBJECTS_DIR)
	$(CC) -S -emit-llvm $(CFLAGS) $< -o $(XMHF_SLAB_OBJECTS_DIR)/$(@F).ll
	cd $(XMHF_SLAB_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	cd $(XMHF_SLAB_OBJECTS_DIR) && llc -O=0 -march=x86-64 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CC) -c $(CFLAGS) $(@F).s -o $(@F)

%.o: %.S
	mkdir -p $(XMHF_SLAB_OBJECTS_DIR)
	cd $(XMHF_SLAB_OBJECTS_DIR) && gcc -c $(CFLAGS) $< -o $(@F)


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_SLAB_OBJECTS_DIR)



