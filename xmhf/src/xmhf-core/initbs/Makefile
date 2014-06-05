# makefile for slabs
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.lscript $(srcdir)

# grab list of all source files
C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES += $(shell find $(srcdir)/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/arch/x86/vmx/ -type f -name '*.c')

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

# grab list of file names only for binary generation
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))

# folder where objects go
SLAB_OBJECTS_DIR = _objs_slab_initbs

# archive name
THE_ARCHIVE = xc-initbs

LINKER_SCRIPT_INPUT := $(srcdir)/xc-initbs.lscript
LINKER_SCRIPT_OUTPUT := xc-initbs.lds


# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS) 
	cd $(SLAB_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) xc-initbs.lscript.c
	cd $(SLAB_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E xc-initbs.lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(SLAB_OBJECTS_DIR) && $(LD) -r --oformat elf32-i386 -T $(LINKER_SCRIPT_OUTPUT) -o $(THE_ARCHIVE).slo $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a

%.o: %.c   
	mkdir -p $(SLAB_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(SLAB_OBJECTS_DIR)/$(@F) $<

.PHONY: clean
clean:
	$(RM) -rf $(SLAB_OBJECTS_DIR)


