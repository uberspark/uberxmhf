SOURCES = visor.c svm.c params.c scode.c ucode.c
SOURCES += intercepts.c
SOURCES += dev.c
ASM_SOURCES = entry.S
OBJECTS = $(patsubst %.c, $(BASEDIR)/$(B_DIR)/%.o, $(SOURCES))
OBJECTS += $(patsubst %.S, $(BASEDIR)/$(B_DIR)/%.o, $(ASM_SOURCES))
DEPS = $(patsubst %.c, $(BASEDIR)/$(B_DIR)/%.d, $(SOURCES))
DEPS += $(patsubst %.S, $(BASEDIR)/$(B_DIR)/%.d, $(ASM_SOURCES))

.PHONY: objs
objs: $(OBJECTS)

# Pattern rule for building dependencies from C sources
$(BASEDIR)/$(B_DIR)/%.d: %.c 	
#@set -e; 
	rm -f $@;\
	$(CC) -M $(CFLAGS) $< > $@.$$$$;\
        sed 's,\($*\)\.o[ :]*,$(BASEDIR)\/$(B_DIR)\/\1.o $@ : ,g' < $@.$$$$ > $@;\
	rm -f $@.$$$$

# Pattern rule for building dependencies from asm sources
$(BASEDIR)/$(B_DIR)/%.d: %.S
#@set -e; 
	rm -f $@;\
	 $(CC) -M $(ASFLAGS) $< > $@.$$$$;\
        sed 's,\($*\)\.o[ :]*,$(BASEDIR)\/$(B_DIR)\/\1.o $@ : ,g' < $@.$$$$ > $@;\
	 rm -f $@.$$$$

ifneq ($(MAKECMDGOALS), clean)
include $(DEPS)
endif

# Pattern rule for builing object files from C sources
$(BASEDIR)/$(B_DIR)/%.o: %.c
#@set -e; 
	$(CC) -c $(CFLAGS) -o $@ $<
	touch $(COMPILE_H)

# Pattern rule for building object files from asm sources
$(BASEDIR)/$(B_DIR)/%.o: %.S
	$(CC) -c $(ASFLAGS) -o $@ $<
	touch $(COMPILE_H)

.PHONY: clean
clean:
	$(RM) -f *~


