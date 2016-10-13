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

# x86 boot-loader is currently 32-bit
CFLAGS += -m32
ASFLAGS += -m32

# folder where objects go
XMHF_BOOTLOADER_OBJECTS_DIR = _objs_xmhf-bootloader
XMHF_BOOTLOADER_LIBS_DIR = _objs_xmhf-bootloader/libs32


# archive name
THE_ARCHIVE = xmhf-bootloader


# targets
.PHONY: all
#all: xmhflibs32 $(THE_ARCHIVE)
all: $(THE_ARCHIVE)


.PHONY: xmhflibs32
xmhflibs32:
	mkdir -p $(XMHF_BOOTLOADER_LIBS_DIR)
	@echo Building XMHF libs 32-bit...
	#cd $(XMHF_BOOTLOADER_LIBS_DIR) && $(MAKE) -f $(XMHFLIBS_SRC)/Makefile -w all
	cd $(XMHF_BOOTLOADER_LIBS_DIR) && $(MAKE) -f $(XMHFLIBS_SRC)/libxmhfdebug/Makefile -w all
	(cd $(XMHF_BOOTLOADER_LIBS_DIR)/_objs_libxmhfdebug && cp *.a ../.) || exit 1;
	#cd $(XMHF_BOOTLOADER_LIBS_DIR) && $(MAKE) -f $(XMHFLIBS_SRC)/libxmhfhw/Makefile -w all
	#(cd $(XMHF_BOOTLOADER_LIBS_DIR)/_objs_libxmhfhw && cp *.a ../.) || exit 1;
	@echo XMHF libs build SUCCESS


$(THE_ARCHIVE): $(OBJECTS)
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/init.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) -L$(CCERT_LIB) -L$(CCLIB)/lib/linux -L$(XMHF_LIBS_OBJECTS_DIR) -lxmhfc -lxmhfdebug -lxmhfcrypto -lxmhfhw -lxmhfc -lcompcert
	#cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/init.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) -L$(CCERT_LIB) -L$(CCLIB)/lib/linux -L./libs32 -lxmhfdebug -lclang_rt.full-i386 -lcompcert
	#cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(STRIP) -s $(THE_ARCHIVE).exe
	cd $(XMHF_BOOTLOADER_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin


%.o: %.S
	mkdir -p $(XMHF_BOOTLOADER_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<"
	gcc -c $(ASFLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$(@F) $<

%.o: %.c
	mkdir -p $(XMHF_BOOTLOADER_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$@ $<
	#$(CC) -c $(CFLAGS) -o $(XMHF_BOOTLOADER_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_BOOTLOADER_OBJECTS_DIR)




