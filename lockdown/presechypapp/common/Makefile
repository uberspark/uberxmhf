################################################################################
# intel vt vmm with v86 monitor
# author: amit vasudevan (amitvasudevan@acm.org)
#
# makefile for common lib
#
# history:
# 10/2/2009 12:25:01 PM  - initial version

# source files
AS_SOURCES = 
C_SOURCES = string.c
OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))
I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<
  
.PHONY: clean 
clean: 
	$(RM) -rf *.o

  
  

  
