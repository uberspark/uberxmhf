# makefile for "runtime"
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

export XMHF_RUNTIME_ARCH_SRC := $(realpath $(srcdir)/arch)

# grab list of all source files
C_SOURCES := $(wildcard $(srcdir)/*.c)
A_SOURCES := 
#C_SOURCES += $(wildcard $(srcdir)/xmhf-apihub/*.c)
#A_SOURCES += $(wildcard $(srcdir)/xmhf-apihub/*.S)
#C_SOURCES += $(shell find $(srcdir)/xmhf-apihub/arch/$(XMHF_CORE_APIHUB_ARCH)/ -type f -name '*.c')
#A_SOURCES += $(shell find $(srcdir)/xmhf-apihub/arch/$(XMHF_CORE_APIHUB_ARCH)/ -type f -name '*.S')

# grab arch. specific sources
#C_SOURCES += $(shell find $(srcdir)/arch/x86/common/ -type f -name '*.c')
#A_SOURCES += $(shell find $(srcdir)/arch/x86/common/ -type f -name '*.S')
#C_SOURCES += $(shell find $(srcdir)/arch/x86/vmx/ -type f -name '*.c')
#A_SOURCES += $(shell find $(srcdir)/arch/x86/vmx/ -type f -name '*.S')
#C_SOURCES += $(shell find $(srcdir)/arch/x86/svm/ -type f -name '*.c')
#A_SOURCES += $(shell find $(srcdir)/arch/x86/svm/ -type f -name '*.S')


C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))
A_SOURCES := $(patsubst $(srcdir)/%, %, $(A_SOURCES))

# grab list of file names only for binary generation
#C_SOURCES_FILENAMEONLY := $(shell find $(srcdir)/ -type f -name '*.c' -printf '%f\n')
#A_SOURCES_FILENAMEONLY := $(shell find $(srcdir)/ -type f -name '*.S' -printf '%f\n')
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))
A_SOURCES_FILENAMEONLY := $(notdir $(A_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))
OBJECTS_ARCHIVE += $(patsubst %.S, %.o, $(A_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.S, %.o, $(A_SOURCES))


OBJECTS_VERIFY := $(patsubst %.c, %.v, $(C_SOURCES))

# additional CFLAGS
# CFLAGS += 

# folder where objects go
XMHF_RUNTIME_OBJECTS_DIR = _objs_xmhf-runtime

# archive name
THE_ARCHIVE = xmhf-runtime

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): libxmhfruntimearch $(OBJECTS) 
	cd $(XMHF_RUNTIME_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/runtime.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) ./_objs_libxmhfruntimearch/libxmhfruntimearch.a $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	cd $(XMHF_RUNTIME_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin


%.o: %.S  
	mkdir -p $(XMHF_RUNTIME_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(XMHF_RUNTIME_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(XMHF_RUNTIME_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(XMHF_RUNTIME_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_RUNTIME_OBJECTS_DIR)


.PHONY: verify
verify: $(OBJECTS_VERIFY)
	mkdir -p $(XMHF_RUNTIME_OBJECTS_DIR)
	cd $(XMHF_RUNTIME_OBJECTS_DIR) && $(MAKE) -f $(XMHF_RUNTIME_ARCH_SRC)/Makefile -w verify
	cd $(XMHF_RUNTIME_OBJECTS_DIR) && echo $(CFLAGS) >CFLAGS
	
%.v: %.c  
	mkdir -p $(XMHF_RUNTIME_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	#@echo Building "$(@F)" from "$<" 
	$(CP) -f $< $(XMHF_RUNTIME_OBJECTS_DIR)/$(@F).c
	

.PHONY: libxmhfruntimearch
libxmhfruntimearch: 
	@echo building libxmhfruntimearch...
	mkdir -p $(XMHF_RUNTIME_OBJECTS_DIR)
	cd $(XMHF_RUNTIME_OBJECTS_DIR) && $(MAKE) -f $(XMHF_RUNTIME_ARCH_SRC)/Makefile -w all
	@echo libxmhfruntimearch build SUCCESS
