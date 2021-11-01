# lockdown hypapp makefile
# author: amit vasudevan (amitvasudevan@acm.org)

SRCDIR := $(dir $(lastword $(MAKEFILE_LIST)))
SRCDIR := $(realpath $(SRCDIR))

export THE_ARCHIVE = xmhfhypapp.a

export APP_INCLUDEDIR = $(SRCDIR)/src/app/include
export APPOBJECTSDIR = $(SRCDIR)/src/app/objects

#-----basic flags for compiling
CFLAGS += -I$(APP_INCLUDEDIR)

export CFLAGS
export ASFLAGS

.PHONY: all
all:
	# make app components
	mkdir -p $(APPOBJECTSDIR)
	cd src && $(MAKE) -w all
	mv ./src/app/$(THE_ARCHIVE) .

.PHONY: clean
clean: 
	cd src && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) $(THE_ARCHIVE)
	rm -f *.bin
	rm -f *.bin.gz

.PHONY: distclean
distclean: clean

