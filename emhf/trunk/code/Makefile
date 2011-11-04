# Rootest Makefile for EMHF and an App
# Builds a bunch of subdirectories here, and then builds the app

# TODO: Consider automating discovery of subdirs (presence of Makefile*?)
# E.g., have a target architecure and include that version of the core
SUBDIRS = libemhfc libemhfutil x86

# TODO: Control this via configure
export APP_ROOT := ../../../trustvisor/trunk/code
# The APP_ARCHIVE is what MUST contain ALL of the App's binary code
# 'make install-dev' is handled indepdendently
export APP_ARCHIVE := $(APP_ROOT)/trustvisor_app.a

export ADDL_INCLUDES := -I$(APP_ROOT)/app/include $(foreach dir,$(SUBDIRS),-I$(CURDIR)/$(dir)/include)


.PHONY: all
all: $(APP_ARCHIVE) subdirs

$(APP_ARCHIVE):
	cd $(APP_ROOT) && $(MAKE) -w all

.PHONY: subdirs
subdirs: $(SUBDIRS)
	@for i in $(SUBDIRS); \
	do \
		(cd $$i && echo "Making all in $$i..." && $(MAKE) -w all) || exit 1; \
	done;

.PHONY: clean
clean:
	cd $(APP_ROOT) && $(MAKE) -w clean
	@for i in $(SUBDIRS) ;\
	do \
		(cd $$i && echo "making clean in $$i..." && $(MAKE) -w clean) || exit 1; \
	done;

.PHONY: install
install: install-dev install-bin

.PHONY: install-bin
install-bin:
	# Install the _actual_ final product

.PHONY: install-dev
install-dev:
	cd $(APP_ROOT) && $(MAKE) -w install-dev
	@for i in $(SUBDIRS) ;\
	do \
		(cd $$i && echo "making install-dev in $$i..." && $(MAKE) -w install-dev) || exit 1; \
	done;
