#-----------------------------------------------------------------------
# lockdown EMHF hyperapp top-level makefile
# author: amit vasudevan (amitvasudevan@acm.org)

export APP_INCLUDEDIR = $(CURDIR)/app/include
export APPOBJECTSDIR = $(CURDIR)/app/objects

CFLAGS += -I$(APP_INCLUDEDIR)

#-----------------------------------------------------------------------
# app-specific configuration options
export LDN_HYPERSWITCHING := y
export LDN_HYPERPARTITIONING := n
export LDN_APPROVEDEXEC := n
export LDN_APPROVEDEXEC_CMPHASHES := y
export LDN_SSLPA := n
export LDN_TV_INTEGRATION := n
	

ifeq ($(LDN_HYPERSWITCHING), y)
  CFLAGS += -D__LDN_HYPERSWITCHING__
endif
ifeq ($(LDN_HYPERPARTITIONING), y)
  CFLAGS += -D__LDN_HYPERPARTITIONING__
endif
ifeq ($(LDN_APPROVEDEXEC), y)
  CFLAGS += -D__LDN_APPROVEDEXEC__
endif
ifeq ($(LDN_APPROVEDEXEC_CMPHASHES), y)
  CFLAGS += -D__LDN_APPROVEDEXEC_CMPHASHES__
endif
ifeq ($(LDN_SSLPA), y)
  CFLAGS += -D__LDN_SSLPA__
endif

#lockdown-trustvisor integration demo
ifeq ($(LDN_TV_INTEGRATION), y)
  CFLAGS += -D__LDN_TV_INTEGRATION__
endif


#-----------------------------------------------------------------------

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

.PHONY: test
test:

.PHONY: clean
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) emhfapp_lockdown.a
	rm -f *.bin
	rm -f *.bin.gz

 
