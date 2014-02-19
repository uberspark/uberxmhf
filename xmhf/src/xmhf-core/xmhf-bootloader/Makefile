# makefile for "init"
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

# grab list of all source files
C_SOURCES := $(shell find $(srcdir)/ -type f -name '*.c')
A_SOURCES := $(shell find $(srcdir)/ -type f -name '*.S')

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))
A_SOURCES := $(patsubst $(srcdir)/%, %, $(A_SOURCES))

# grab list of file names only for binary generation
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))
A_SOURCES_FILENAMEONLY := $(notdir $(A_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))
OBJECTS_ARCHIVE += $(patsubst %.S, %.o, $(A_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.S, %.o, $(A_SOURCES))

# additional CFLAGS
# CFLAGS += 
# RUNTIME_INTEGRITY_HASH should be set by parent Makefile
ifdef RUNTIME_INTEGRITY_HASH
CFLAGS += -D___RUNTIME_INTEGRITY_HASH___=\"$(RUNTIME_INTEGRITY_HASH)\"
endif
# SLABOVE64K_INTEGRITY_HASH should be set by parent Makefile
ifdef SLABOVE64K_INTEGRITY_HASH
CFLAGS += -D___SLABOVE64K_INTEGRITY_HASH___=\"$(SLABOVE64K_INTEGRITY_HASH)\"
endif
# SLBELOW64K_INTEGRITY_HASH should be set by parent Makefile
ifdef SLBELOW64K_INTEGRITY_HASH
CFLAGS += -D___SLBELOW64K_INTEGRITY_HASH___=\"$(SLBELOW64K_INTEGRITY_HASH)\"
endif

# folder where objects go
XMHF_BOOTLOADER_OBJECTS_DIR = _objs_xmhf-bootloader

# archive name
THE_ARCHIVE = xmhf-bootloader


# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS) 
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/init.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(STRIP) -s $(THE_ARCHIVE).exe
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin


%.o: %.S  
	mkdir -p $(XMHF_BOOTLOADER_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(XMHF_BOOTLOADER_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_BOOTLOADER_OBJECTS_DIR)




