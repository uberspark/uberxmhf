# makefile for emhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  
C_SOURCES = memp-interface.c
C_SOURCES += ./arch/x86/memp-x86.c

C_SOURCES += ./arch/x86/vmx/memp-x86vmx.c
C_SOURCES += ./arch/x86/vmx/memp-x86vmx-data.c

C_SOURCES += ./arch/x86/svm/memp-x86svm.c
C_SOURCES += ./arch/x86/svm/memp-x86svm-data.c

V_SOURCES = memp-interface.c
V_SOURCES += ./arch/x86/memp-x86.c
V_SOURCES += ./arch/x86/vmx/memp-x86vmx.c
V_SOURCES += ./arch/x86/svm/memp-x86svm.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# Awful, awful.  FIXME!
CFLAGS += -I../../../libemhfc/include/

# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf ./arch/vmx/*.o
	$(RM) -rf ./arch/svm/*.o
 
.PHONY: verify 
verify: 
	cbmc $(VFLAGS) -D__EMHF_VERIFICATION__ --bounds-check --pointer-check ./verification/emhf-memprot-vdriver.c 
	# $(V_SOURCES)
	
  

  
