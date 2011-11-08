#-------------------------------------------------------------------------------
# Makefile for EMHF apps
# author: amit vasudevan (amitvasudevan@acm.org)

# change this to whatever you want your EMHF app to be called
export TARGET_ARCHIVE = ../emhfapp_helloworld.a

# generate app INCLUDE and OBJECT directories
export APP_INCLUDEDIR = $(CURDIR)/app/include
export APPOBJECTSDIR = $(CURDIR)/app/objects

#-----basic flags for compiling
CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
CFLAGS += -fno-stack-protector
CFLAGS += -Wimplicit-function-declaration
CFLAGS += -Wall
CFLAGS += -Wparentheses
CFLAGS += -Wunused
CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare 
CFLAGS += -Waggregate-return
CFLAGS += -Winline
CFLAGS += -m32 -march=k8
CFLAGS += -mno-sse2
CFLAGS += -nostdinc -pipe -I$(EMHF_INCLUDE) -I$(APP_INCLUDEDIR) $(ADDL_INCLUDES)

#-----generate compiler/assembler defines from configuration options selected
ifeq ($(NESTED_PAGING), y)
CFLAGS += -D__NESTED_PAGING__
endif
ifeq ($(DEBUG_SERIAL), y)
CFLAGS += -D__DEBUG_SERIAL__
CFLAGS += -DDEBUG_PORT=$(DEBUG_SERIAL_PORT)
endif
ifeq ($(DEBUG_VGA), y)
CFLAGS += -D__DEBUG_VGA__
endif
ifeq ($(MP_VERSION), y)
CFLAGS += -D__MP_VERSION__
endif

ASFLAGS = $(CFLAGS) -D__ASSEMBLY__

export CFLAGS
export ASFLAGS

.PHONY: all
all:
	# make app components
	mkdir -p $(APPOBJECTSDIR)
	cd app && $(MAKE) -w all

# There is no binary installation; only the EMHF core
# produces a complete binary of some sort.  All libraries
# are at the root level as well.
.PHONY: install
install: 

# install development headers (if any)
.PHONY: install-dev
install-dev:
	
# perform unit tests (if any)
.PHONY: test
test:
	
# cleanup
.PHONY: clean
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) $(TARGET_ARCHIVE)
	rm -f *.bin
	rm -f *.bin.gz

