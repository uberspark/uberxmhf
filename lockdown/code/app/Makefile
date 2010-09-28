#-------------------------------------------------------------------------------
# app top-level makefile for apps based on sechyp
# author: amit vasudevan (amitvasudevan@acm.org)

# app-specific configuration options
export LDN_HYPERSWITCHING := y
export LDN_HYPERPARTITIONING := y
export LDN_APPROVEDEXEC := y
export LDN_SSLPA := y


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





# source files
AS_SOURCES = 
C_SOURCES = appmain.c acpi.c hp_sdisk_ata.c 

ifeq ($(LDN_APPROVEDEXEC), y)
C_SOURCES += approvedexec.c approvedexec_windows.c sha1.c
endif

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES  =  $(wildcard $(SECHYP_INCLUDEDIR)/*.h)
I_SOURCES  +=  $(wildcard $(APP_INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $(APPOBJECTSDIR)/$@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $(APPOBJECTSDIR)/$@ $<
  
.PHONY: clean 
clean: 

  
  

  
