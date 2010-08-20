#-------------------------------------------------------------------------------
# app top-level makefile for apps based on sechyp
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 
C_SOURCES = appmain.c acpi.c hp_sdisk_ata.c

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

  
  

  
