# makefile for xmhf-memprot (EMHF memory protection component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES = memp-interface.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/memp-$(TARGET_HWPLATFORM).c

C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/memp-$(TARGET_HWPLATFORM)vmx.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/memp-$(TARGET_HWPLATFORM)vmx-data.c

C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/memp-$(TARGET_HWPLATFORM)svm.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/memp-$(TARGET_HWPLATFORM)svm-data.c


OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

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
	$(RM) -rf ./arch/*/*.o
	$(RM) -rf ./arch/*/vmx/*.o
	$(RM) -rf ./arch/*/svm/*.o

