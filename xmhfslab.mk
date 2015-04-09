# common makefile for slabs
# author: amit vasudevan (amitvasudevan@acm.org)


XMHF_SLAB_SOURCES_SUBST := $(patsubst $(srcdir)/%, %, $(XMHF_SLAB_SOURCES))

# grab list of file names only for binary generation
XMHF_SLAB_SOURCES_FILENAMEONLY := $(notdir $(XMHF_SLAB_SOURCES_SUBST))

XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(XMHF_SLAB_SOURCES_FILENAMEONLY))
XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.cS, %.o, $(XMHF_SLAB_OBJECTS_ARCHIVE))
XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.S, %.o, $(XMHF_SLAB_OBJECTS_ARCHIVE))

# list of object dependencies
XMHF_SLAB_OBJECTS := $(patsubst %.c, %.o, $(XMHF_SLAB_SOURCES_SUBST))
XMHF_SLAB_OBJECTS := $(patsubst %.cS, %.o, $(XMHF_SLAB_OBJECTS))
XMHF_SLAB_OBJECTS := $(patsubst %.S, %.o, $(XMHF_SLAB_OBJECTS))

# folder where objects go
XMHF_SLAB_OBJECTS_DIR := _objs_slab_$(XMHF_SLAB_NAME)

LINKER_SCRIPT_INPUT := $(XMHF_DIR)/xmhfslab.lscript
LINKER_SCRIPT_OUTPUT := $(XMHF_SLAB_NAME).lds

#XMHF_SLAB_STUBOBJECTS := $(XMHFLIBS_DIR)/xmhfgeec_slabmap.o $(XMHFLIBS_DIR)/xmhfgeec_tprogslab.o

# populate slab stub type based on the slab type
ifeq ($(XMHF_SLAB_TYPE), tprogslab)
	XMHF_SLAB_STUBOBJECTS := $(XMHFLIBS_DIR)/xmhfgeec_slabmap.o $(XMHFLIBS_DIR)/xmhfgeec_tprogslab.o
endif

ifeq ($(XMHF_SLAB_TYPE), ugprogslab)
	XMHF_SLAB_STUBOBJECTS := $(XMHFLIBS_DIR)/xmhfgeec_slabmap.o $(XMHFLIBS_DIR)/xmhfgeec_tprogslab.o
endif


# targets
.PHONY: all
all: buildslabbin

buildslabbin: $(XMHF_SLAB_OBJECTS)
	cd $(XMHF_SLAB_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) $(XMHF_SLAB_NAME).lscript.c
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E $(XMHF_SLAB_NAME).lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(LD) -r --oformat elf32-i386 -T $(LINKER_SCRIPT_OUTPUT) -o $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_OBJECTS_ARCHIVE) $(XMHF_SLAB_STUBOBJECTS) -L$(CCERT_LIB) -L$(CCLIB)/lib/linux -L$(XMHFLIBS_DIR) -lxmhfc -lxmhfcrypto -lxmhfhw -lxmhfhw -lxmhfc -lclang_rt.full-i386 -lcompcert
	cd $(XMHF_SLAB_OBJECTS_DIR) && nm $(XMHF_SLAB_NAME).slo | awk '{ print $$3 }' | awk NF >$(XMHF_SLAB_NAME).slo.syms
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(OBJCOPY) --localize-symbols=$(XMHF_SLAB_NAME).slo.syms $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_NAME).slo
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(OBJCOPY) $(XMHF_SLAB_GLOBAL_SYMS) $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_NAME).slo


%.o: %.c
	mkdir -p $(XMHF_SLAB_OBJECTS_DIR)
	$(CCERT) -c $(CCERT_FLAGS) -o $(XMHF_SLAB_OBJECTS_DIR)/$@ $<

%.o: %.cS
	mkdir -p $(XMHF_SLAB_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	cp -f $< $(XMHF_SLAB_OBJECTS_DIR)/$(@F).c
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_FLAGS) $(@F).c
	cd $(XMHF_SLAB_OBJECTS_DIR) && extractasm.pl $(@F).mach > $(@F).S
	cd $(XMHF_SLAB_OBJECTS_DIR) && gcc -c $(ASFLAGS) -o $@ $(@F).S

%.o: %.S
	mkdir -p $(XMHF_SLAB_OBJECTS_DIR)
	cd $(XMHF_SLAB_OBJECTS_DIR) && gcc -c $(ASFLAGS) $< -o $(@F)


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_SLAB_OBJECTS_DIR)



