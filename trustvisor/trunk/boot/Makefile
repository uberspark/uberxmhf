SOURCES = boot.S 
OBJECTS = $(patsubst %.S, $(BASEDIR)/$(B_DIR)/%.o, $(SOURCES))
DEPS = $(patsubst %.S, $(BASEDIR)/$(B_DIR)/%.d, $(SOURCES))

$(BASEDIR)/$(B_DIR)/$(TARGET).gz: $(BASEDIR)/$(B_DIR)/$(TARGET) $(CHK_INIT)
	$(BASEDIR)/$(B_DIR)/chk_init
	gzip -f -9 < $< > $@.new
	mv $@.new $@
#cp $@ /boot

$(BASEDIR)/$(B_DIR)/$(TARGET): $(MKELF) $(BASEDIR)/$(B_DIR)/$(TARGET)-syms
	$(BASEDIR)/$(B_DIR)/mkelf32 $@-syms $@-elf 0x1e00000 `$(NM) -nr $@-syms |\
	 head -n 1 | sed -e 's/^\([^ ]*\).*/0x\1/'`
	$(OBJCOPY) $(OBJCOPYFLAGS) $@-elf $@

$(CHK_INIT): chk_init_size.c $(BASEDIR)/$(B_DIR)/init_size.h
	$(CC) $(HOSTCFLAGS) -o $@ $<

$(BASEDIR)/$(B_DIR)/init_size.h: $(BASEDIR)/$(B_DIR)/System.map
	$(SED) s/ADDR1/`grep _visor_init_start $(BASEDIR)/$(B_DIR)/System.map | awk '{print $$1}'`/ $(INCLUDE_DIR)/init_size.h.template > $@.1
	$(SED) s/ADDR2/`grep _visor_init_end $(BASEDIR)/$(B_DIR)/System.map | awk '{print $$1}'`/ $@.1 > $@

$(BASEDIR)/$(B_DIR)/System.map: $(BASEDIR)/$(B_DIR)/$(TARGET)-syms
	$(NM) -n $(BASEDIR)/$(B_DIR)/$(TARGET)-syms | \
	grep -vE '(\.[[:digit:]]+)' > $@

$(BASEDIR)/$(B_DIR)/$(TARGET)-syms: $(LINKER_SCRIPT) $(OBJECTS) $(COMPILE_H) 
	$(LD) -T $(LINKER_SCRIPT) -o $@ $(BASEDIR)/$(B_DIR)/*.o
	$(OBJDUMP) -D $@ > $(BASEDIR)/$(B_DIR)/$(TARGET).bin

$(MKELF): mkelf32.c 
	$(CC) $(HOSTCFLAGS) -o $@ $<

# -P: do not emit line markers during preprocessing
# -E: stop after preprocessing
# -Ui386: cancel any previous defn of i386
$(LINKER_SCRIPT): $(BASEDIR)/visor.lds.S $(BASEDIR)/include/visor.h \
$(BASEDIR)/include/paging.h
	$(CC) -P -E -Ui386 $(ASFLAGS) -o $@ $< 

# Pattern rules for building dependencies and object files from 
# asm sources
$(BASEDIR)/$(B_DIR)/%.d: %.S
#@set -e; 
	rm -f $@;\
	 $(CC) -M $(ASFLAGS) $< > $@.$$$$;\
         sed 's,\($*\)\.o[ :]*,$(BASEDIR)\/$(B_DIR)\/\1.o $@ : ,g' < $@.$$$$ > $@;\
	 rm -f $@.$$$$

ifneq ($(MAKECMDGOALS), clean)
include $(DEPS)
endif

$(BASEDIR)/$(B_DIR)/%.o: %.S
	$(CC) -c $(ASFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) -f *~
