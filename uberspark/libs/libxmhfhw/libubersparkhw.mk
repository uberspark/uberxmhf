######
# libubersparkhw Makefile
# author: amit vasudevan (amitvasudevan@acm.org)
######

###### archive name
ARCHIVE = libubersparkhw.a

###### compute source directory where this Makefile resides
srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)


###### populate sources and objects
C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
CS_SOURCES:= $(wildcard $(srcdir)/*.cS)
CS_SOURCES:= $(patsubst $(srcdir)/%, %, $(CS_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.cS, %.o, $(CS_SOURCES))
CS_CINTERMEDIATE_SOURCES := $(patsubst %.cS, %.o.c, $(CS_SOURCES))
CS_ASMINTERMEDIATE_SOURCES := $(patsubst %.cS, %.o.S, $(CS_SOURCES))
CS_MACHINTERMEDIATE_SOURCES := $(patsubst %.cS, %.o.mach, $(CS_SOURCES))


# targets

.PHONY: verify-with-wp
verify-with-wp:
	#$(FRAMAC) -wp -main fls -lib-entry -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_fls.c
	#$(FRAMAC) -main __getsec_capabilities -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getseccaps.c
	#$(FRAMAC) -main __getsec_parameters -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getsecparams.c
	#$(FRAMAC) -main __getsec_senter -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getsecsenter.c
	#$(FRAMAC) -main __getsec_sexit -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getsecsexit.c
	#$(FRAMAC) -main __getsec_smctrl -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getsecsmctrl.c
	#$(FRAMAC) -main __getsec_wakeup -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getsecwakeup.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_getcpuvendor -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_getvendor.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_x86_cpuhasxsavefeature -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_hasxsave.c
	#$(FRAMAC) -main set_all_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_mtrrenabledisable.c
	#$(FRAMAC) -main xmhfhw_cpu_x86_restore_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_mtrrrestore.c
	#$(FRAMAC) -main xmhfhw_cpu_x86_save_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_mtrrsave.c
	#$(FRAMAC) -main set_mem_type -lib-entry -wp -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_mtrrsetmemtype.c
	#$(FRAMAC) -main validate_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_mtrrvalidate.c
	#$(FRAMAC) -main get_bios_data_size -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetbiosdatasize.c
	#$(FRAMAC) -main get_bios_data_start -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetbiosdatastart.c
	#$(FRAMAC) -main get_txt_heap -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetheap.c
	#$(FRAMAC) -main get_os_mle_data_size -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetosmledatasize.c
	#$(FRAMAC) -main get_os_mle_data_start -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetosmledatastart.c
	#$(FRAMAC) -main get_os_sinit_data_size -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetossinitdatasize.c
	#$(FRAMAC) -main get_os_sinit_data_start -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetossinitdatastart.c
	#$(FRAMAC) -main get_sinit_mle_data_size -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetsinitmledatasize.c
	#$(FRAMAC) -main get_sinit_mle_data_start -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtgetsinitmledatastart.c
	#$(FRAMAC) -main txt_is_launched -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtislaunched.c
	#$(FRAMAC) -main read_priv_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtreadprivcr.c
	#$(FRAMAC) -main read_pub_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtreadpubcr.c
	#$(FRAMAC) -main write_priv_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtwriteprivcr.c
	#$(FRAMAC) -main write_pub_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_cpu_txtwritepubcr.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_x86_reboot -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_keyb_reboot.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_x86_getcpulapicid -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_lapic_getid.c
	#$(FRAMAC) -main xmhfhw_lapic_isbsp -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_lapic_isbsp.c
	#$(FRAMAC) -main xmhfhw_platform_bus_init -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_pci_initbus.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_x86_pci_type1_read -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_pci_read.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_x86_pci_type1_write -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_pci_write.c
	#$(FRAMAC) -main xmhf_baseplatform_arch_x86_udelay -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_pit_udelay.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_acpi_getRSDP -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_sysmem_getacpirsdp.c
	#$(FRAMAC) -main _vtd_reg_read -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_readreg.c
	#$(FRAMAC) -main _vtd_reg_write -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_writereg.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_disable_pmr -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_disablepmr.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_disable_translation -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_disabletrans.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_enable_translation -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_enabletrans.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_initialize -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_initdrhd.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_invlcaches.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_setphm.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_setplm.c
	#$(FRAMAC) -main xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/xmhfhw_vtd_setret.c


.PHONY: verify-with-val
verify-with-val:
	#$(CP) -f $(srcdir)/../libxmhfgeec/xmhfgeec_slabmapdef.c xmhfgeec_slabmapdef.c
	#$(CP) -f $(srcdir)/xmhfhw_cpu_bsrl.cS xmhfhw_cpu_bsrl.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_bsrl.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_cpuid.cS xmhfhw_cpu_cpuid.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_cpuid.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_disableintr.cS xmhfhw_cpu_disableintr.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_disableintr.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_enableintr.cS xmhfhw_cpu_enableintr.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_enableintr.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_getgdtbase.cS xmhfhw_cpu_getgdtbase.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_getgdtbase.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_getidtbase.cS xmhfhw_cpu_getidtbase.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_getidtbase.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_getsec.cS xmhfhw_cpu_getsec.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_getsec.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_gettssbase.cS xmhfhw_cpu_gettssbase.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_gettssbase.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_inb.cS xmhfhw_cpu_inb.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_inb.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_inl.cS xmhfhw_cpu_inl.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_inl.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_invept.cS xmhfhw_cpu_invept.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_invept.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_invvpid.cS xmhfhw_cpu_invvpid.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_invvpid.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_inw.cS xmhfhw_cpu_inw.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_inw.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_loadgdt.cS xmhfhw_cpu_loadgdt.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_loadgdt.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_loadidt.cS xmhfhw_cpu_loadidt.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_loadidt.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_loadtr.cS xmhfhw_cpu_loadtr.cS.c
	#$(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_loadtr.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_outb.cS xmhfhw_cpu_outb.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_outb.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_outl.cS xmhfhw_cpu_outl.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_outl.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_outw.cS xmhfhw_cpu_outw.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_outw.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_pause.cS xmhfhw_cpu_pause.cS.c
	#frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_pause.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	@for i in $(CS_SOURCES); \
	do \
		($(CP) -f $(srcdir)/$$i $$i.c) || exit 1; \
	done;
	@echo Sources prepped.
	$(FRAMAC) -val -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c *.cS.c $(USPARK_INSTALL_HWMDIR)/*.c
	@for i in $(CS_SOURCES); \
	do \
		($(RM) $$i.c) || exit 1; \
	done;


.PHONY: verify
verify: verify-with-val
	

.PHONY: build
build: $(ARCHIVE)

$(ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(ARCHIVE) $(OBJECTS)

%.o: %.c
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_CFLAGS) -o $@ $<

%.o: %.cS
	@echo Building "$@" from "$<"
	$(CP) -f $< $(@F).c
	$(CCERT) -c -dmach $(CCERT_CASMFLAGS) $(@F).c
	$(FRAMAC) -load-module $(USPARK_INSTALL_TOOLSDIR)/Ucasm -ucasm-infile $(@F).mach -ucasm-outfile $(@F).S
	$(CC) -c $(ASMFLAGS) -o $@ $(@F).S



.PHONY: clean
clean:
	$(RM) $(OBJECTS)
	$(RM) $(CS_CINTERMEDIATE_SOURCES)
	$(RM) $(CS_ASMINTERMEDIATE_SOURCES)
	$(RM) $(CS_MACHINTERMEDIATE_SOURCES)
	$(RM) $(ARCHIVE)
	@for i in $(CS_SOURCES); \
	do \
		($(RM) $$i.c) || exit 1; \
	done;
	


