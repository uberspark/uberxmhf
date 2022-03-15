# makefile for xmhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES = dmap-interface-earlyinit.c dmap-interface-runtime.c iommu-pt.c
C_SOURCES += ./arch/x86/dmap-x86-earlyinit.c
C_SOURCES += ./arch/x86/dmap-x86-runtime.c
C_SOURCES += ./arch/x86/svm/dmap-svm.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-earlyinit.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-internal.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-runtime.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-utils.c
C_SOURCES += ./arch/x86/vmx/dmap-vmx-data.c

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)
	# Optional: use sparse file to reduce fs space usage
	fallocate -d ./arch/x86/vmx/dmap-vmx-data.o

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) -rf *.o
	$(RM) -rf ./arch/*/*.o
	$(RM) -rf ./arch/*/svm/*.o
	$(RM) -rf ./arch/*/vmx/*.o

