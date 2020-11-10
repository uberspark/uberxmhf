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
export XMHF_SLAB_SUBTYPE := PRIME
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


export XMHF_SLAB_NAME := geec_prime
export XMHF_SLAB_SOURCES := $(wildcard $(srcdir)/*.c)
XMHF_SLAB_SOURCES += $(wildcard $(srcdir)/*.cS)

#export XMHF_SLAB_FULLLINK := n

export XMHF_SLAB_GLOBAL_SYMS :=
########################################################################






.PHONY: verify
verify: verifybase verif_s1 verif_s2 verif_s3 verif_s4 verif_s5

.PHONY: verif_s1
verif_s1: 
	@echo Verifying stage-1...
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s1_bspstack -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s1_bspstack.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main _gp_s1_bspstack_getflagsforspa -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s1_bspstackgetflags.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s1_bspstkactivate.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s1_chkreq.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s1_entry.cS.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s1_hub -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s1_hub.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s1_iommuinit.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/xmhfhw_vtd*.c.v.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s1_iommuinittbl -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s1_iommuinittbl.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s1_iommuinittblclearcet -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s1_iommuinittblclearcet.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s1_postdrt.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c libxmhfhw/xmhfhw_cpu_txt*.c.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s1_scaniommu.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/xmhfhw_sysmem_getacpirsdp.c.v.c libxmhfhw/xmhfhw_vtd_readreg.c.v.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	

.PHONY: verif_s2
verif_s2: 
	@echo Verifying stage-2...
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_entry -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_s2_entry.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s2_gathersysmemtypes.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s2_initsysmemmap.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sda -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sda.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdabinddevice -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdabinddevice.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdadoalloc_getuobjfordev -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdadoalloc_getuobjfordev.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdadoalloc -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdadoalloc.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdasetupdevpgtbl_rg -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdasetupdevpgtbl_rg.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdasetupdevpgtbl_setptentries -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdasetupdevpgtbl_setptentries.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdasetupdevpgtbl_splintpdt -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdasetupdevpgtbl_splintpdt.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdasetupdevpgtbl -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdasetupdevpgtbl.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdmenumsysdevices_memioextents -lib-entry -wp -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdmenumsysdevices_memioextents.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdmenumsysdevices -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdmenumsysdevices.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdminitdevmap_addalldevstouobj -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdminitdevmap_addalldevstouobj.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdminitdevmap_adddeventry -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdminitdevmap_adddeventry.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdminitdevmap_adddevtouobj -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdminitdevmap_adddevtouobj.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdminitdevmap_isdevinexcl -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdminitdevmap_isdevinexcl.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_sdminitdevmap -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_sdminitdevmap.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupgdt -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupgdt.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupgdt_setgdttssentry -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupgdttssentry.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupidt -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupidt.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupiotbl -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupiotbl.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupiotblug_rg -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupiotblug_rg.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupiotblug -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupiotblug.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupiotblug_allowaccesstoport -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupiotblugportaccess.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupiotbluh -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupiotbluh.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupiotbluh_allowaccesstoport -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupiotbluhportaccess.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbl_getspatype -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbl_getspatype.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbl_getspatypeuobj_isiotbl -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbl_getspatypeuobj_isiotbl.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbl_getspatypeuobj_ismmio -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbl_getspatypeuobj_ismmio.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbl_getspatypeuobj -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbl_getspatypeuobj.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtblu -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblu.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtblug_getflags -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblug_getflags.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblug_getmtype.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtblug_rg -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblug_rg.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtblug -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblug.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbluh_getflags -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbluh_getflags.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbluh_setentry -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbluh_setentry.c.v.c
#	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtbluh -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtbluh.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtblv_getflags -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblv_getflags.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setupmpgtblv -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setupmpgtblv.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setuptss -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setuptss.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s2_setuptss_inittss -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s2_setuptssinittss.c.v.c

.PHONY: verif_s3
verif_s3: 
	@echo Verifying stage-3...
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s3_entry -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s3_entry.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -pp-annot -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s3_startcores.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/xmhfhw_cpu_txt*.c.v.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)

.PHONY: verif_s4
verif_s4: 
	@echo Verifying stage-4...
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s4_apstacks.cS.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s4_entry.cS.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)

.PHONY: verif_s5
verif_s5: 
	@echo Verifying stage-5...
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -main gp_s5_entry -lib-entry -wp -wp-rte -wp-model +cint+cast  -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) gp_data.c.v.c gp_s5_entry.c.v.c
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s5_invokestrt.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)
	cd $(XMHF_SLAB_VERIFICATION_DIR) && frama-c -no-frama-c-stdlib -val -no-val-show-progress -slevel 2048 -cpp-extra-args=-nostdinc -cpp-extra-args=-D__USPARK_FRAMAC_VA__ $(VFLAGS) gp_data.c.v.c gp_s5_setupcpustate.c.v.c xmhfgeec_slabinfotable.c xmhfgeec_slabmapdef.c libxmhfhw/*.c.v.c libxmhfhw/*.cS.v.c $(V_XMHFHWM_MODULES)



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








