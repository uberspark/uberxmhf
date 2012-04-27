#-----------------------------------------------------------------------
# lockdown EMHF hyperapp top-level makefile
# author: amit vasudevan (amitvasudevan@acm.org)

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

#-----------------------------------------------------------------------
# app-specific configuration options
export LDN_HYPERSWITCHING := y
export LDN_HYPERPARTITIONING := n
export LDN_APPROVEDEXEC := y
export LDN_APPROVEDEXEC_CMPHASHES := y
export LDN_SSLPA := n
	

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

 
