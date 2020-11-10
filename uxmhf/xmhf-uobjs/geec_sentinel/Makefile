# common makefile for slabs
# author: amit vasudevan (amitvasudevan@acm.org)
export srcdir := $(dir $(lastword $(MAKEFILE_LIST)))

vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.cS $(srcdir)
vpath %.lscript $(srcdir)

include $(srcdir)/../../uxmhf-common.mk

export XMHF_SLAB_FULLLINK := y
export XMHF_SLAB_TYPE := VfT_SLAB
export XMHF_SLAB_SUBTYPE := SENTINEL
export XMHF_SLAB_MAIN := slab_main

# populate slab stub type based on the slab type
ifeq ($(XMHF_SLAB_TYPE), VfT_SLAB)

    ifeq ($(XMHF_SLAB_SUBTYPE), SENTINEL)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), PRIME)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), UAPI)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), INIT)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), EXCEPTION)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), INTERCEPT)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), XCORE)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), XHYPAPP)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    #else ifeq ($(XMHF_SLAB_SUBTYPE), XGUEST)
    #    XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_vft.o
    else
        #unsupported slab sub-type
        XMHF_SLAB_STUBOBJECTS :=
    endif


else ifeq ($(XMHF_SLAB_TYPE), uVT_SLAB)


    ifeq ($(XMHF_SLAB_SUBTYPE), INIT)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_uvt.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), XCORE)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_uvt.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), XHYPAPP)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_uvt.o
    #else ifeq ($(XMHF_SLAB_SUBTYPE), XGUEST)
    #    XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_uvtg.o
    else
        #unsupported slab sub-type
        XMHF_SLAB_STUBOBJECTS :=
    endif


else ifeq ($(XMHF_SLAB_TYPE), uVU_SLAB)


    ifeq ($(XMHF_SLAB_SUBTYPE), XHYPAPP)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_uvu.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), XGUEST)
        XMHF_SLAB_STUBOBJECTS := $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabmapdef.o $(XMHF_OBJDIR)/uobjinfotable.o $(USPARK_INSTALL_LIBSDIR)/xmhfgeec_slabstubs_uvug.o
    else ifeq ($(XMHF_SLAB_SUBTYPE), XRICHGUEST)
        XMHF_SLAB_STUBOBJECTS := 
    else
        #unsupported slab sub-type
        XMHF_SLAB_STUBOBJECTS :=
    endif


else

    #unsupported slab type
    XMHF_SLAB_STUBOBJECTS :=

endif


########################################################################
#
# options that each slab will customize
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################


export XMHF_SLAB_NAME := geec_sentinel
export XMHF_SLAB_MAIN :=_slab_entrystub
export XMHF_SLAB_SOURCES := $(wildcard $(srcdir)/*.c)
XMHF_SLAB_SOURCES += $(wildcard $(srcdir)/*.cS)

#export XMHF_SLAB_FULLLINK := n

export XMHF_SLAB_GLOBAL_SYMS :=

########################################################################


.PHONY: verify
verify: verifybase
	@echo Proceeding to verify $(XMHF_SLAB_NAME)...
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATHV2V $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_callstub*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATHV2UV $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_callstub*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATHV2UG $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_callstub*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATH_RETEXCP $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_callstub*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATH_RETICPT $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_callstub*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATH_RETUH2VH $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_callstub*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATH_CALLUH2VH $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_syscall*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ -cpp-extra-args=-DDRV_PATH_RETVH2UH $(VFLAGS) xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c gs_entry_syscall*.c gs_data.c.v.c gs_entry.c.v.c gs_exit_*.c gs_siss*.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gs_siss_push -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gs_data.c.v.c gs_sisspush.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gs_siss_pop -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gs_data.c.v.c gs_sisspop.c.v.c



# common makefile for slabs
# author: amit vasudevan (amitvasudevan@acm.org)

XMHF_SLAB_SOURCES_SUBST := $(patsubst $(srcdir)/%, %, $(XMHF_SLAB_SOURCES))

# grab list of file names only for binary generation
XMHF_SLAB_SOURCES_FILENAMEONLY := $(notdir $(XMHF_SLAB_SOURCES_SUBST))

XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(XMHF_SLAB_SOURCES_FILENAMEONLY))
XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.cS, %.o, $(XMHF_SLAB_OBJECTS_ARCHIVE))
XMHF_SLAB_OBJECTS_ARCHIVE := $(patsubst %.S, %.o, $(XMHF_SLAB_OBJECTS_ARCHIVE))

XMHF_SLAB_VERIFICATION_SOURCES := $(patsubst %.c, %.c.v.c, $(XMHF_SLAB_SOURCES_FILENAMEONLY))
XMHF_SLAB_VERIFICATION_SOURCES := $(patsubst %.cS, %.cS.v.c, $(XMHF_SLAB_VERIFICATION_SOURCES))


# list of object dependencies
XMHF_SLAB_OBJECTS := $(patsubst %.c, %.o, $(XMHF_SLAB_SOURCES_SUBST))
XMHF_SLAB_OBJECTS := $(patsubst %.cS, %.o, $(XMHF_SLAB_OBJECTS))
XMHF_SLAB_OBJECTS := $(patsubst %.S, %.o, $(XMHF_SLAB_OBJECTS))

# folder where objects go
XMHF_SLAB_OBJECTS_DIR := _objs_slab_$(XMHF_SLAB_NAME)
XMHF_SLAB_VERIFICATION_DIR := _verif_$(XMHF_SLAB_NAME)

LINKER_SCRIPT_INPUT := $(XMHF_DIR)/xmhf-uobjs/$(XMHF_SLAB_NAME)/xmhfgeecslab.lscript
LINKER_SCRIPT_OUTPUT := $(XMHF_SLAB_NAME).lds

#ifeq ($(XMHF_SLAB_FULLLINK), y)
export LDFLAGS := --oformat elf32-i386
#else

#endif

# targets
ifeq ($(XMHF_SLAB_SUBTYPE), XRICHGUEST)

.PHONY: all
all: 
	@echo Nothing to compile for rich guest object

else

.PHONY: all
all: buildslabbin

endif


#uspark
.PHONY: verifybase
verifybase:
	@echo Prepping sources...
	$(MKDIR) -p $(XMHF_SLAB_VERIFICATION_DIR)
	@for i in $(XMHF_SLAB_SOURCES_SUBST); \
	do \
		($(CP) -f $$i $(XMHF_SLAB_VERIFICATION_DIR)/$$i.v.c) || exit 1; \
	done;
	$(CP) -f $(XMHF_OBJDIR)/_verif_bp/$(XMHF_SLAB_NAME)_sstub.ag.v.c $(XMHF_SLAB_VERIFICATION_DIR)/.
	$(CP) -f $(V_LIBXMHFGEEC_MODULES_DIR)/xmhfgeec_slabmapdef.c $(XMHF_SLAB_VERIFICATION_DIR)/.
	$(CP) -f $(XMHF_OBJDIR)/uobjinfotable.c $(XMHF_SLAB_VERIFICATION_DIR)/xmhfgeec_slabinfotable.c
	$(MKDIR) -p $(XMHF_SLAB_VERIFICATION_DIR)/libxmhfhw
	@for i in $(V_LIBXMHFHW_MODULES); \
	do \
		($(CP) -f $(V_LIBXMHFHW_MODULES_DIR)/$$i $(XMHF_SLAB_VERIFICATION_DIR)/libxmhfhw/$$i.v.c) || exit 1; \
	done;
	@echo Sources prepped.


ifeq ($(XMHF_SLAB_SUBTYPE), XRICHGUEST)

.PHONY: linkslabbin
linkslabbin:
	@echo Nothing to link for rich guest object

else

.PHONY: linkslabbin
linkslabbin:
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CP) -f $(LINKER_SCRIPT_INPUT) $(XMHF_SLAB_NAME).lscript.c
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CC) -E -P $(ASMFLAGS) $(XMHF_SLAB_NAME).lscript.c -o $(LINKER_SCRIPT_OUTPUT)
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(LD) $(LDFLAGS) -T $(LINKER_SCRIPT_OUTPUT) -o $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_OBJECTS_ARCHIVE) $(XMHF_SLAB_STUBOBJECTS) -L$(CCERT_LIB) -L$(XMHF_LIBS_OBJECTS_DIR) -L$(USPARK_INSTALL_LIBSDIR) -lubersparkc -lubersparkcrypto -lxmhfdebug -lubersparkhw -lubersparkc -lcompcert
	cd $(XMHF_SLAB_OBJECTS_DIR) && nm $(XMHF_SLAB_NAME).slo | awk '{ print $$3 }' | awk NF >$(XMHF_SLAB_NAME).slo.syms
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(OBJCOPY) --localize-symbols=$(XMHF_SLAB_NAME).slo.syms $(XMHF_SLAB_NAME).slo $(XMHF_SLAB_NAME).slo
	cd $(XMHF_SLAB_OBJECTS_DIR) && nm $(XMHF_SLAB_NAME).slo | awk '{ print $$3,":",$$1 }' | awk NF >$(XMHF_SLAB_NAME).mmap

endif


buildslabbin: $(XMHF_SLAB_OBJECTS) linkslabbin

%.o: %.c
	$(MKDIR) -p $(XMHF_SLAB_OBJECTS_DIR)
	$(CCERT) -c $(CCERT_CFLAGS) -o $(XMHF_SLAB_OBJECTS_DIR)/$@ $<

%.o: %.cS
	$(MKDIR) -p $(XMHF_SLAB_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CP) -f $< $(XMHF_SLAB_OBJECTS_DIR)/$(@F).c
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_CASMFLAGS) $(@F).c
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(FRAMAC) -load-module $(USPARK_INSTALL_TOOLSDIR)/Ucasm -ucasm-infile $(@F).mach -ucasm-outfile $(@F).S
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CC) -c $(ASMFLAGS) -o $@ $(@F).S


%.o: %.S
	mkdir -p $(XMHF_SLAB_OBJECTS_DIR)
	cd $(XMHF_SLAB_OBJECTS_DIR) && $(CC) -c $(ASMFLAGS) $< -o $(@F)

.PHONY: clean
clean:
	$(RM) -rf $(XMHF_SLAB_OBJECTS_DIR)








