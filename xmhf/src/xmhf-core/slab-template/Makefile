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


# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS) 
	cd $(SLAB_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) xmhf-slab.lscript.c
	cd $(SLAB_OBJECTS_DIR) && $(CC) -P -E xmhf-slab.lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(SLAB_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(LINKER_SCRIPT_OUTPUT) -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	cd $(SLAB_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin

%.o: %.c   
	mkdir -p $(SLAB_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(SLAB_OBJECTS_DIR)/$(@F) $<

.PHONY: clean
clean:
	$(RM) -rf $(SLAB_OBJECTS_DIR)


