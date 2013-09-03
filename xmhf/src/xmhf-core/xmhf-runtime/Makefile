# makefile for "runtime"
# author: amit vasudevan (amitvasudevan@acm.org)

# targets
.PHONY: all
all: runtime.bin

runtime.bin: $(OBJECTS) $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(OBJECTS_PRECOMPILED_LIBBACKENDS) runtime.lds.S
	$(LD) -T runtime.lds.S -o runtime.exe $(OBJECTS) $(OBJECTS_PRECOMPILED) $(APP_ARCHIVE) $(ADDL_LIBS) $(OBJECTS_PRECOMPILED_LIBBACKENDS) -L$(CCLIB) -lgcc
	$(OBJCOPY) --output-format=binary runtime.exe runtime.bin

%.o: %.S $(I_SOURCES) Makefile ../../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../../Makefile 
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf ./arch/x86/*.o
	$(RM) -rf *.exe
	$(RM) -rf *.bin
	$(RM) -rf *.gz
