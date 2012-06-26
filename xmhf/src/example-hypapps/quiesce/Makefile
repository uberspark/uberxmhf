#-------------------------------------------------------------------------------
# Makefile for XMHF apps
# author: amit vasudevan (amitvasudevan@acm.org)

# change this to whatever you want your EMHF app to be called
export TARGET_ARCHIVE = ../xmhfapp_quiesce.a

# generate app INCLUDE and OBJECT directories
export APP_INCLUDEDIR = $(CURDIR)/app/include
export APPOBJECTSDIR = $(CURDIR)/app/objects

CFLAGS += -I$(APP_INCLUDEDIR)

export CFLAGS
export ASFLAGS

.PHONY: all
all:
	# make app components
	mkdir -p $(APPOBJECTSDIR)
	cd app && $(MAKE) -w all

# There is no binary installation; only the XMHF core
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

