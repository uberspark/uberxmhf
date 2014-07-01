# Makefile for libxcshared
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree build)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

vpath %.c $(srcdir)

# grab list of all source files
C_SOURCES := $(shell find $(srcdir)/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/arch/x86/common/ -type f -name '*.c')

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

CFLAGS += -nostdinc -fno-builtin -nostdlib -Wall 

LIBXCSHARED_OBJECTS_DIR = _objs_libxcshared
THE_ARCHIVE = libxcshared.a

# LLC flags
LLC_ATTR = -3dnow,-3dnowa,-64bit,-64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop

.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXCSHARED_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS_ARCHIVE)

%.o: %.c   
	mkdir -p $(LIBXCSHARED_OBJECTS_DIR)
	#mkdir -p "$(@D)"
	@echo Building "$(@F)" from "$<" 
	$(CC) -S -emit-llvm $(CFLAGS) $< -o $(LIBXCSHARED_OBJECTS_DIR)/$(@F).ll
	cd $(LIBXCSHARED_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	cd $(LIBXCSHARED_OBJECTS_DIR) && llc -O=0 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(LIBXCSHARED_OBJECTS_DIR) && $(CC) -c $(CFLAGS) $(@F).s -o $(@F)


.PHONY: clean
clean:
	$(RM) -rf $(LIBXCSHARED_OBJECTS_DIR)

