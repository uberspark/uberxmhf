SOURCES = heap.c visor_pt.c nested_pt.c
OBJECTS = $(patsubst %.c, $(BASEDIR)/$(B_DIR)/%.o, $(SOURCES))
DEPS = $(patsubst %.c, $(BASEDIR)/$(B_DIR)/%.d, $(SOURCES))

.PHONY: objs
objs: $(OBJECTS)

# Pattern rule for building dependencies from C sources
$(BASEDIR)/$(B_DIR)/%.d: %.c 	
#@set -e; 
	rm -f $@;\
	$(CC) -M $(CFLAGS) $< > $@.$$$$;\
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

.PHONY: clean
clean:
	$(RM) -f *~


