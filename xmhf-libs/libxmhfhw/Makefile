# Makefile for hw
# will end up building libxmhfplatform and libxmhfcpu
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree build)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

vpath %.c $(srcdir)

# grab list of all source files
C_SOURCES := $(shell find $(srcdir)/cpu/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/cpu/x86/intel/ -type f -name '*.c')

C_SOURCES += $(shell find $(srcdir)/platform/x86pc/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/platform/x86pc/intel/ -type f -name '*.c')

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

#C_SOURCES_FILENAMEONLY := $(shell find $(srcdir)/cpu/x86/ -type f -name '*.c' -printf '%f\n')
#C_SOURCES_FILENAMEONLY += $(shell find $(srcdir)/platform/x86pc/ -type f -name '*.c' -printf '%f\n')

OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS_VERIFY := $(patsubst %.c, %.v, $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

I_SOURCES := $(shell find $(srcdir)/cpu/x86/include/ -type f -name '*.h')
I_SOURCES += $(shell find $(srcdir)/platform/x86pc/include/ -type f -name '*.h')

CFLAGS += -nostdinc -fno-builtin -nostdlib -Wall 

LIBXMHFHW_OBJECTS_DIR = _objs_libxmhfhw
THE_ARCHIVE = libxmhfhw.a

.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFHW_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS_ARCHIVE)

%.o: %.S  
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(LIBXMHFHW_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBXMHFHW_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFHW_OBJECTS_DIR)

.PHONY: verify
verify: $(OBJECTS_VERIFY)
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	cd $(LIBXMHFHW_OBJECTS_DIR) && echo $(CFLAGS) >CFLAGS
	
%.v: %.c  
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	#@echo Building "$(@F)" from "$<" 
	$(CP) -f $< $(LIBXMHFHW_OBJECTS_DIR)/$(@F).c
	
