# makefile for slabs
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.lscript $(srcdir)

# grab list of all source files
C_SOURCES := $(wildcard $(srcdir)/*.c)

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

# grab list of file names only for binary generation
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))

# folder where objects go
SLAB_OBJECTS_DIR = _objs_slab

# archive name
THE_ARCHIVE = xmhf-slab

LINKER_SCRIPT_INPUT := $(srcdir)/xmhf-slab.lscript
LINKER_SCRIPT_OUTPUT := xmhf-slab.lds


# LLC flags
LLC_ATTR = -3dnow,-3dnowa,-64bit,-64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS) 
	cd $(SLAB_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) xmhf-slab.lscript.c
	cd $(SLAB_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E xmhf-slab.lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(SLAB_OBJECTS_DIR) && $(LD) -r --oformat elf32-i386 -T $(LINKER_SCRIPT_OUTPUT) -o $(THE_ARCHIVE).slo $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	#cd $(SLAB_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).slbin

#%.o: %.c   
#	mkdir -p $(SLAB_OBJECTS_DIR)
#	@echo Building "$(@F)" from "$<" 
#	$(CC) -c $(CFLAGS) -o $(SLAB_OBJECTS_DIR)/$(@F) $<
	
%.o: %.c   
	$(CC) -S -emit-llvm $(CFLAGS) $< -o $(SLAB_OBJECTS_DIR)/$(@F).ll
	cd $(SLAB_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	cd $(SLAB_OBJECTS_DIR) && llc -O=0 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(SLAB_OBJECTS_DIR) && $(CC) -c $(CFLAGS) $(@F).s -o $(@F)


.PHONY: clean
clean:
	$(RM) -rf $(SLAB_OBJECTS_DIR)


