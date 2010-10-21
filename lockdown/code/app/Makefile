#-------------------------------------------------------------------------------
# app top-level makefile for apps based on sechyp
# author: amit vasudevan (amitvasudevan@acm.org)

# app-specific configuration options
export LDN_HYPERSWITCHING := y
export LDN_HYPERPARTITIONING := n
export LDN_APPROVEDEXEC := n
export LDN_SSLPA := n
# test modes
	# fwreset, experiment with minimal device reset and cycle through GRUB
	export LDN_TEST_FWRESET	:=	n
	# mload, experiment with manual bzImage/initrd-ramfs load without GRUB
	export LDN_TEST_MLOAD	:=	y
	

ifeq ($(LDN_HYPERSWITCHING), y)
  CFLAGS += -D__LDN_HYPERSWITCHING__
endif
ifeq ($(LDN_HYPERPARTITIONING), y)
  CFLAGS += -D__LDN_HYPERPARTITIONING__
endif
ifeq ($(LDN_APPROVEDEXEC), y)
  CFLAGS += -D__LDN_APPROVEDEXEC__
endif
ifeq ($(LDN_SSLPA), y)
  CFLAGS += -D__LDN_SSLPA__
endif

ifeq ($(LDN_TEST_FWRESET), y)
  CFLAGS += -D__LDN_TEST_FWRESET__
endif
ifeq ($(LDN_TEST_MLOAD), y)
  CFLAGS += -D__LDN_TEST_MLOAD__
endif




# source files
AS_SOURCES = 
C_SOURCES = appmain.c acpi.c hp_sdisk_ata.c fwreset.c linuxrelc.c

ifeq ($(LDN_APPROVEDEXEC), y)
C_SOURCES += approvedexec.c approvedexec_windows.c sha1.c
endif

OBJECTS = $(patsubst %.S, $(APPOBJECTSDIR)/%.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, $(APPOBJECTSDIR)/%.o, $(C_SOURCES))

I_SOURCES  =  $(wildcard $(SECHYP_INCLUDEDIR)/*.h)
I_SOURCES  +=  $(wildcard $(APP_INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

$(APPOBJECTSDIR)/%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
$(APPOBJECTSDIR)/%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<
  
.PHONY: clean 
clean: 

  
  

  
