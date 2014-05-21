# makefile for XMHF core
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

# grab list of all source files
C_SOURCES := $(wildcard $(srcdir)/*.c)

C_SOURCES += $(wildcard $(srcdir)/initbs/*.c)
C_SOURCES += $(shell find $(srcdir)/initbs/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/initbs/arch/x86/vmx/ -type f -name '*.c')

C_SOURCES += $(wildcard $(srcdir)/shared/*.c)

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

# grab list of file names only for binary generation
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))

# folder where objects go
XMHF_CORE_OBJECTS_DIR = _objs_xmhf-core

# archive name
THE_ARCHIVE = xmhf-core

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS) 
	cd $(XMHF_CORE_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/xc.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	cd $(XMHF_CORE_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin

%.o: %.c   
	mkdir -p $(XMHF_CORE_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(XMHF_CORE_OBJECTS_DIR)/$(@F) $<

.PHONY: clean
clean:
	$(RM) -rf $(XMHF_CORE_OBJECTS_DIR)


