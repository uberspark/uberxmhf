# export EMHFCOREDIR := $(CURDIR)/../../../emhf/trunk/code/$(EMHFROOTDIR)/x86
# export EMHF_INCLUDEDIR = $(EMHFCOREDIR)/include

SRCDIR := $(dir $(lastword $(MAKEFILE_LIST)))
SRCDIR := $(realpath $(SRCDIR))

# TODO: Control via configuration
export THE_ARCHIVE = emhfapp.a

export APP_INCLUDEDIR = $(SRCDIR)/src/include
export APPOBJECTSDIR = $(SRCDIR)/src/objects

#-----basic flags for compiling
CFLAGS += -I$(APP_INCLUDEDIR)

# app-specific configuration options
export LDN_TV_INTEGRATION := n

#lockdown-trustvisor integration demo
ifeq ($(LDN_TV_INTEGRATION), y)
  CFLAGS += -D__LDN_TV_INTEGRATION__
endif

export CFLAGS
export ASFLAGS

.PHONY: all
all:
	# make app components
	mkdir -p $(APPOBJECTSDIR)
	cd src && $(MAKE) -w all

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
	install $(SRCDIR)/src/include/trustvisor.h $(DESTDIR)$(includedir)/trustvisor
	install $(LIBBAREMETAL_SRC)/libtv_utpm/include/tv_utpm.h $(DESTDIR)$(includedir)/trustvisor

.PHONY: test
test:
	cd test && $(MAKE) -w all

.PHONY: clean
clean: 
	cd src && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) $(THE_ARCHIVE)
	cd test && $(MAKE) -w clean
	rm -f *.bin
	rm -f *.bin.gz

