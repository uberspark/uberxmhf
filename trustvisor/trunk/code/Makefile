# export EMHFCOREDIR := $(CURDIR)/../../../emhf/trunk/code/$(EMHFROOTDIR)/x86
# export EMHF_INCLUDEDIR = $(EMHFCOREDIR)/include

# TODO: Control via configuration
export THE_ARCHIVE = app_trustvisor.a

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
# CFLAGS += -nostdinc -pipe -I$(EMHF_INCLUDEDIR) -I$(APP_INCLUDEDIR) $(ADDL_INCLUDES)
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
install: install-dev

# install development components
.PHONY: install-dev
install-dev:
	install -d $(DESTDIR)$(pkgconfigdir)
	install --mode=644 trustvisor.pc $(DESTDIR)$(pkgconfigdir)

	install -d $(DESTDIR)$(includedir)/trustvisor
	install app/include/trustvisor.h $(DESTDIR)$(includedir)/trustvisor

.PHONY: test
test:
	cd test && $(MAKE) -w all

.PHONY: clean
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) $(THE_ARCHIVE)
	cd test && $(MAKE) -w clean
	rm -f *.bin
	rm -f *.bin.gz

