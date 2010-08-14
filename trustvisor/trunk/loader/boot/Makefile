AS_SOURCES = boot.S
C_SOURCES = e820.c relocate.c string.c skinit.c ucode.c loader_uart.c loader_sha1.c
OBJECTS = $(patsubst %.S, $(BASEDIR)/$(B_DIR)/%.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, $(BASEDIR)/$(B_DIR)/%.o, $(C_SOURCES))
DEPS = $(patsubst %.S, $(BASEDIR)/$(B_DIR)/%.d, $(AS_SOURCES))
DEPS += $(patsubst %.c, $(BASEDIR)/$(B_DIR)/%.d, $(C_SOURCES))

$(BASEDIR)/$(B_DIR)/$(TARGET).gz: $(BASEDIR)/$(B_DIR)/$(TARGET)
	gzip -f -9 < $< > $@.new
	mv $@.new $@

$(BASEDIR)/$(B_DIR)/$(TARGET): $(MKELF) $(LINKER_SCRIPT) $(OBJECTS)
	$(LD) -T $(LINKER_SCRIPT) -o $@-syms $(BASEDIR)/$(B_DIR)/*.o
	$(OBJDUMP) -D $@-syms > $@.bin
	$(NM) -n $@-syms | grep -vE '(\.[[:digit:]]+)' > \
	$(BASEDIR)/$(B_DIR)/System.map
	$(BASEDIR)/$(B_DIR)/mkelf32 $@-syms $@ 0x1800000 \
        `$(NM) -nr $@-syms | head -n 1 | sed -e 's/^\([^ ]*\).*/0x\1/'`

$(MKELF): mkelf32.c 
	$(CC) $(HOSTCFLAGS) -o $@ $<

# -P: do not emit line markers during preprocessing
# -E: stop after preprocessing
# -Ui386: cancel any previous defn of i386
$(LINKER_SCRIPT): $(BASEDIR)/loader.lds.S $(BASEDIR)/../include/paging.h
	$(CC) -P -E -Ui386 $(ASFLAGS) -o $@ $< 

# Pattern rules for building dependencies and object files from 
# asm and C sources
$(BASEDIR)/$(B_DIR)/%.d: %.S
#@set -e; 
	rm -f $@;\
	 $(CC) -M $(ASFLAGS) $< > $@.$$$$;\
         sed 's,\($*\)\.o[ :]*,$(BASEDIR)\/$(B_DIR)\/\1.o $@ : ,g' < $@.$$$$ > $@;\
	 rm -f $@.$$$$
$(BASEDIR)/$(B_DIR)/%.d: %.c 	
#@set -e; 
	rm -f $@;\
	$(CC) -M $(CFLAGS) $< > $@.$$$$;\
        sed 's,\($*\)\.o[ :]*,$(BASEDIR)\/$(B_DIR)\/\1.o $@ : ,g' < $@.$$$$ > $@;\
	rm -f $@.$$$$

ifneq ($(MAKECMDGOALS), clean)
include $(DEPS)
endif

$(BASEDIR)/$(B_DIR)/%.o: %.S
	$(CC) -c $(ASFLAGS) -o $@ $<
$(BASEDIR)/$(B_DIR)/%.o: %.c
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) -f *~
