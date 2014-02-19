# makefile for "sl"
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

export XMHF_SECURELOADER_ARCH_SRC := $(realpath $(srcdir)/arch)


# grab list of all source files
C_SOURCES := $(wildcard $(srcdir)/*.c)

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

# grab list of file names only for binary generation
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_VERIFY := $(patsubst %.c, %.v, $(C_SOURCES))

# additional CFLAGS
# CFLAGS += 
# RUNTIME_INTEGRITY_HASH should be set by parent Makefile
ifdef RUNTIME_INTEGRITY_HASH
CFLAGS += -D___RUNTIME_INTEGRITY_HASH___=\"$(RUNTIME_INTEGRITY_HASH)\"
endif

# folder where objects go
XMHF_SECURELOADER_OBJECTS_DIR = _objs_xmhf-secureloader

# archive name
THE_ARCHIVE = xmhf-secureloader


# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): libxmhfslarch $(OBJECTS) 
	cd $(XMHF_SECURELOADER_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/sl.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) ./_objs_libxmhfslarch/libxmhfslarch.a $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	#cd $(XMHF_SECURELOADER_OBJECTS_DIR) && $(STRIP) -s $(THE_ARCHIVE).exe
	cd $(XMHF_SECURELOADER_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin


%.o: %.S  
	mkdir -p $(XMHF_SECURELOADER_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(XMHF_SECURELOADER_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(XMHF_SECURELOADER_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(XMHF_SECURELOADER_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_SECURELOADER_OBJECTS_DIR)


.PHONY: verify
verify: $(OBJECTS_VERIFY)
	mkdir -p $(XMHF_SECURELOADER_OBJECTS_DIR)
	cd $(XMHF_SECURELOADER_OBJECTS_DIR) && $(MAKE) -f $(XMHF_SECURELOADER_ARCH_SRC)/Makefile -w verify
	cd $(XMHF_SECURELOADER_OBJECTS_DIR) && echo $(CFLAGS) >CFLAGS
	
%.v: %.c  
	mkdir -p $(XMHF_SECURELOADER_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	#@echo Building "$(@F)" from "$<" 
	$(CP) -f $< $(XMHF_SECURELOADER_OBJECTS_DIR)/$(@F).c

.PHONY: libxmhfslarch
libxmhfslarch: 
	@echo building libxmhfslarch...
	mkdir -p $(XMHF_SECURELOADER_OBJECTS_DIR)
	cd $(XMHF_SECURELOADER_OBJECTS_DIR) && $(MAKE) -f $(XMHF_SECURELOADER_ARCH_SRC)/Makefile -w all
	@echo libxmhfslarch build SUCCESS
