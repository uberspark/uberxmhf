# makefile for xmhf bootloader
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


# folder where objects go
XMHF_BOOTLOADER_OBJECTS_DIR = _objs_xmhf-bootloader

# archive name
THE_ARCHIVE = xmhf-bootloader

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/init.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) -L$(CCERT_LIB) -L$(XMHF_LIBS_OBJECTS_DIR) -L$(USPARK_INSTALL_LIBSDIR) -lubersparkc -lxmhfdebug -lubersparkcrypto -lubersparkhw -lubersparkc -lcompcert
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin

%.o: %.S
	$(MKDIR) -p $(XMHF_BOOTLOADER_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<"
	$(CC) -c $(ASMFLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$(@F) $<

%.o: %.c
	$(MKDIR) -p $(XMHF_BOOTLOADER_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<"
	$(CCERT) -c $(CCERT_CFLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$@ $<


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_BOOTLOADER_OBJECTS_DIR)




