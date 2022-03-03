# makefile for xmhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES = dmap-interface.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/dmap-$(TARGET_HWPLATFORM).c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/dmap-$(TARGET_HWPLATFORM)svm.c

C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/dmap-$(TARGET_HWPLATFORM)vmx.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/dmap-$(TARGET_HWPLATFORM)vmx-data.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)
	# Optional: use sparse file to reduce fs space usage
	fallocate -d ./arch/$(TARGET_HWPLATFORM)/vmx/dmap-$(TARGET_HWPLATFORM)vmx-data.o

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

