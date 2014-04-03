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

# grab list of all source files
C_SOURCES := $(shell find $(srcdir)/ -type f -name '*.c')
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))
A_SOURCES := $(shell find $(srcdir)/ -type f -name '*.S')
A_SOURCES := $(patsubst $(srcdir)/%, %, $(A_SOURCES))

# grab list of file names only for archive generation
C_SOURCES_FILENAMEONLY := $(shell find $(srcdir)/ -type f -name '*.c' -printf '%f\n')
A_SOURCES_FILENAMEONLY := $(shell find $(srcdir)/ -type f -name '*.S' -printf '%f\n')
OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))
OBJECTS_ARCHIVE += $(patsubst %.S, %.o, $(A_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.S, %.o, $(A_SOURCES))

OBJECTS_VERIFY := $(patsubst %.c, %.v, $(C_SOURCES))

# additional CFLAGS
CFLAGS += -nostdinc -fno-builtin -nostdlib -Wall 

# folder where objects go
#LIBBAREMETAL_XMHFBACKENDS_OBJECTS_DIR = _objs_libbaremetal-xmhfbackends
LIBXMHFDEBUG_OBJECTS_DIR = _objs_libxmhfdebug

# archive name
#THE_ARCHIVE = libbaremetal-xmhfbackends.a
THE_ARCHIVE = libxmhfdebug.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFDEBUG_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS_ARCHIVE)

%.o: %.S  
	mkdir -p $(LIBXMHFDEBUG_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	gcc -c $(ASFLAGS) -o $(LIBXMHFDEBUG_OBJECTS_DIR)/$(@F) $<

%.o: %.c   
	mkdir -p $(LIBXMHFDEBUG_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBXMHFDEBUG_OBJECTS_DIR)/$(@F) $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFDEBUG_OBJECTS_DIR)
	
.PHONY: verify
verify: $(OBJECTS_VERIFY)
	mkdir -p $(LIBXMHFDEBUG_OBJECTS_DIR)
	cd $(LIBXMHFDEBUG_OBJECTS_DIR) && echo $(CFLAGS) >CFLAGS
	
%.v: %.c  
	mkdir -p $(LIBXMHFDEBUG_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	#@echo Building "$(@F)" from "$<" 
	$(CP) -f $< $(LIBXMHFDEBUG_OBJECTS_DIR)/$(@F).c
