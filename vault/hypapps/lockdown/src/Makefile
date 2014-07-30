#-----------------------------------------------------------------------
# makefile for Lockdown XMHF hypapp
# author: amit vasudevan (amitvasudevan@acm.org)
#

# source files
AS_SOURCES = 
C_SOURCES = appmain.c approvedexec.c hyperpart-switch.c hyperpart-disk.c approvedexec-windows.c
I_SOURCES =  $(wildcard ./include/*.h)

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

CFLAGS += -I./include

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
# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.S $(I_SOURCES) Makefile  
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile 
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -	f *.o

