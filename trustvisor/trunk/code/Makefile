export TARGET = trustvisor
export TARGET_HWPLATFORM := x86
export NESTED_PAGING := y

# TODO: THESE SHOULD BE PASSED IN FROM THE CORE BUILD OR SET USING ./configure
ifeq ($(TARGET_HWPLATFORM), x86)
export EMHFROOTDIR := ../../../emhf/trunk/code
export EMHFCOREDIR := $(EMHFROOTDIR)/x86
endif

export EMHFUTILDIR := $(EMHFROOTDIR)/libemhfutil
export EMHFCDIR := $(EMHFROOTDIR)/libemhfc
export EMHFCRYPTODIR := $(EMHFROOTDIR)/libemhfcrypto
export TV_UTPMDIR := $(EMHFROOTDIR)/libtv_utpm

export BASEDIR = /home/jmmccune/work/hyp.git/trustvisor/trunk/code
export APPOBJECTSDIR = $(BASEDIR)/app/objects
export EMHF_INCLUDEDIR = $(BASEDIR)/$(EMHFCOREDIR)/include
export EMHFUTIL_INCLUDEDIR = $(BASEDIR)/$(EMHFUTILDIR)/include
export EMHFC_INCLUDEDIR = $(BASEDIR)/$(EMHFCDIR)/include
export EMHFCRYPTO_INCLUDEDIR = $(BASEDIR)/$(EMHFCRYPTODIR)/include
export TV_UTPM_INCLUDEDIR = $(BASEDIR)/$(TV_UTPMDIR)/include
export INCLUDEDIR = $(EMHF_INCLUDEDIR)
export APP_INCLUDEDIR = $(BASEDIR)/app/include
export EMHFAPP = y

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
CFLAGS += -nostdinc -pipe -I$(EMHF_INCLUDEDIR) -I$(APP_INCLUDEDIR) -I$(EMHFUTIL_INCLUDEDIR) -I$(EMHFC_INCLUDEDIR) -I$(EMHFCRYPTO_INCLUDEDIR)
CFLAGS += -I$(TV_UTPM_INCLUDEDIR)

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

	install -d $(DESTDIR)$(pkgincludedir)
	install app/include/trustvisor.h $(DESTDIR)$(pkgincludedir)

.PHONY: test
test:
	cd test && $(MAKE) -w all

.PHONY: clean
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) app_trustvisor.a
	cd test && $(MAKE) -w clean
	rm -f *.bin
	rm -f *.bin.gz

