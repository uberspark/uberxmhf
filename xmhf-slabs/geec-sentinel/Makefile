########################################################################
#
# Makefile for XMHF GEEC sentinel
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export srcdir := $(dir $(lastword $(MAKEFILE_LIST)))

vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.lscript $(srcdir)
vpath %.cS $(srcdir)

########################################################################

export XMHF_GEECSENTINEL_NAME := geec-sentinel
export XMHF_GEECSENTINEL_SOURCES := $(wildcard $(srcdir)/*.c)
XMHF_GEECSENTINEL_SOURCES += $(wildcard $(srcdir)/*.cS)


########################################################################
# generic build harness

XMHF_GEECSENTINEL_SOURCES_SUBST := $(patsubst $(srcdir)/%, %, $(XMHF_GEECSENTINEL_SOURCES))

# grab list of file names only for binary generation
XMHF_GEECSENTINEL_SOURCES_FILENAMEONLY := $(notdir $(XMHF_GEECSENTINEL_SOURCES_SUBST))

XMHF_GEECSENTINEL_OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(XMHF_GEECSENTINEL_SOURCES_FILENAMEONLY))
XMHF_GEECSENTINEL_OBJECTS_ARCHIVE := $(patsubst %.cS, %.o, $(XMHF_GEECSENTINEL_OBJECTS_ARCHIVE))

# list of object dependencies
XMHF_GEECSENTINEL_OBJECTS := $(patsubst %.c, %.o, $(XMHF_GEECSENTINEL_SOURCES_SUBST))
XMHF_GEECSENTINEL_OBJECTS := $(patsubst %.cS, %.o, $(XMHF_GEECSENTINEL_OBJECTS))

# folder where objects go
XMHF_GEECSENTINEL_OBJECTS_DIR := _objs_$(XMHF_GEECSENTINEL_NAME)

LINKER_SCRIPT_INPUT := $(XMHF_DIR)/xmhf-slabs/geec-sentinel/geec-sentinel.lscript
LINKER_SCRIPT_OUTPUT := $(XMHF_GEECSENTINEL_NAME).lds

# targets
.PHONY: all
all: buildgeecsentinelbin

buildgeecsentinelbin: $(XMHF_GEECSENTINEL_OBJECTS)
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && cp -f $(LINKER_SCRIPT_INPUT) $(XMHF_GEECSENTINEL_NAME).lscript.c
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E $(XMHF_GEECSENTINEL_NAME).lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && $(LD) -r --oformat elf32-i386 -T $(LINKER_SCRIPT_OUTPUT) -o $(XMHF_GEECSENTINEL_NAME).slo $(XMHF_GEECSENTINEL_OBJECTS_ARCHIVE) -L$(CCERT_LIB) -L$(CCLIB)/lib/linux -L$(XMHFLIBS_DIR) -lxmhfc -lxmhfcrypto -lxmhfdebug -lxmhfhw -whole-archive -lxmhfhicslab -no-whole-archive -lxmhfc -lclang_rt.full-i386 -lcompcert
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && nm $(XMHF_GEECSENTINEL_NAME).slo | awk '{ print $$3 }' | awk NF >$(XMHF_GEECSENTINEL_NAME).slo.syms
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && $(OBJCOPY) --localize-symbols=$(XMHF_GEECSENTINEL_NAME).slo.syms $(XMHF_GEECSENTINEL_NAME).slo $(XMHF_GEECSENTINEL_NAME).slo
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && $(OBJCOPY) --globalize-symbol __xmhfhic_rtm_intercept --globalize-symbol __xmhfhic_rtm_exception_stub --globalize-symbol __xmhfhic_rtm_trampoline --globalize-symbol __xmhfhic_rtm_uapihandler $(XMHF_GEECSENTINEL_NAME).slo $(XMHF_GEECSENTINEL_NAME).slo

%.o: %.c
	mkdir -p $(XMHF_GEECSENTINEL_OBJECTS_DIR)
	$(CCERT) -c $(CCERT_FLAGS) -o $(XMHF_GEECSENTINEL_OBJECTS_DIR)/$@ $<

%.o: %.cS
	mkdir -p $(XMHF_GEECSENTINEL_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	cp -f $< $(XMHF_GEECSENTINEL_OBJECTS_DIR)/$(@F).c
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_FLAGS) $(@F).c
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && extractasm.pl $(@F).mach > $(@F).S
	cd $(XMHF_GEECSENTINEL_OBJECTS_DIR) && gcc -c $(ASFLAGS) -o $@ $(@F).S


.PHONY: clean
clean:
	$(RM) -rf $(XMHF_GEECSENTINEL_OBJECTS_DIR)




