#
# XMHF core secure loader arch. backend
#
# author: amit vasudevan (amitvasudevan@acm.org)
#
# builds libxmhfslarch.a which is then linked into xmhf-secureloader
#

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

# grab list of all source files
C_SOURCES := $(shell find $(srcdir)/x86/common/ -type f -name '*.c')
A_SOURCES := $(shell find $(srcdir)/x86/common/ -type f -name '*.S')

C_SOURCES += $(shell find $(srcdir)/x86/vmx/ -type f -name '*.c')
A_SOURCES += $(shell find $(srcdir)/x86/vmx/ -type f -name '*.S')

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))
A_SOURCES := $(patsubst $(srcdir)/%, %, $(A_SOURCES))

OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.S, %.o, $(A_SOURCES))

OBJECTS_VERIFY := $(patsubst %.c, %.v, $(C_SOURCES))

OBJECTS_ARCHIVE := $(notdir $(OBJECTS))

LIBXMHFSLARCH_OBJECTS_DIR = _objs_libxmhfslarch
THE_ARCHIVE = libxmhfslarch.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFSLARCH_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS_ARCHIVE)

%.o: %.S  
	mkdir -p $(LIBXMHFSLARCH_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(LIBXMHFSLARCH_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(LIBXMHFSLARCH_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBXMHFSLARCH_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFSLARCH_OBJECTS_DIR)
	
.PHONY: verify
verify: $(OBJECTS_VERIFY)
	mkdir -p $(LIBXMHFSLARCH_OBJECTS_DIR)
	cd $(LIBXMHFSLARCH_OBJECTS_DIR) && echo $(CFLAGS) >CFLAGS
	
%.v: %.c  
	mkdir -p $(LIBXMHFSLARCH_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	#@echo Building "$(@F)" from "$<" 
	$(CP) -f $< $(LIBXMHFSLARCH_OBJECTS_DIR)/$(@F).c
