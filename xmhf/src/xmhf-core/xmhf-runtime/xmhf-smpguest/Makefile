# makefile for xmhf-smpguest (EMHF SMP guest component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =
C_SOURCES = smpg-interface.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/smpg-$(TARGET_HWPLATFORM).c

C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/smpg-$(TARGET_HWPLATFORM)svm.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/svm/smpg-$(TARGET_HWPLATFORM)svm-data.c

C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/smpg-$(TARGET_HWPLATFORM)vmx.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/smpg-$(TARGET_HWPLATFORM)vmx-data.c


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

