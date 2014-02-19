#
# libxmhfcore - XMHF core interface library
#
# author: amit vasudevan (amitvasudevan@acm.org)
#
# note: designed to operate on out-of-tree builds
#

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

C_SOURCES := $(wildcard $(srcdir)/*.c)
A_SOURCES := $(wildcard $(srcdir)/*.S)

C_SOURCES += $(wildcard $(srcdir)/arch/$(XMHF_CORE_APIHUB_ARCH)/*.c)
A_SOURCES += $(wildcard $(srcdir)/arch/$(XMHF_CORE_APIHUB_ARCH)/*.S)

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.S, %.o, $(A_SOURCES))
OBJECTS := $(patsubst $(srcdir)/%, %, $(OBJECTS))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall 

LIBXMHFCORE_OBJECTS_DIR = _objs_libxmhfcore
THE_ARCHIVE = libxmhfcore.a


# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFCORE_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(patsubst arch/$(XMHF_CORE_APIHUB_ARCH)/%, %, $(OBJECTS))

%.o: %.S  
	mkdir -p $(LIBXMHFCORE_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(LIBXMHFCORE_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(LIBXMHFCORE_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBXMHFCORE_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFCORE_OBJECTS_DIR)
	
