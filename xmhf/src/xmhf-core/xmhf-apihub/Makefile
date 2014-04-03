# makefile for xmhf-apihub (XMHF core API interface component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files

C_SOURCES = ./apih-interface.c
C_SOURCES += $(wildcard ./arch/$(XMHF_CORE_APIHUB_ARCH)/*.c) 
AS_SOURCES = 
AS_SOURCES += $(wildcard ./arch/$(XMHF_CORE_APIHUB_ARCH)/*.S) 


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
		$(RM) -f *.o
		$(RM) -f ./arch/swfp/*.o
		$(RM) -f ./arch/pbvph/*.o
 
  
  

  
