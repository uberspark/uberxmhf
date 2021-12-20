# makefile for xmhf-parteventhub (EMHF partition event-hub component)
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = ./arch/$(TARGET_HWPLATFORM)/svm/peh-$(TARGET_HWPLATFORM)svm-entry.S
AS_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/peh-$(TARGET_HWPLATFORM)vmx-entry.S

C_SOURCES =  ./arch/$(TARGET_HWPLATFORM)/svm/peh-$(TARGET_HWPLATFORM)svm-main.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/peh-$(TARGET_HWPLATFORM)vmx-main.c
C_SOURCES += ./arch/$(TARGET_HWPLATFORM)/vmx/peh-$(TARGET_HWPLATFORM)-safemsr.c

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
	$(RM) -rf ./arch/*/svm/*.o
	$(RM) -rf ./arch/*/vmx/*.o

