srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)

include $(srcdir)/../../common.mk


C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

CS_SOURCES:= $(wildcard $(srcdir)/*.cS)
CS_SOURCES:= $(patsubst $(srcdir)/%, %, $(CS_SOURCES))


OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.cS, %.o, $(CS_SOURCES))


I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFHW_OBJECTS_DIR = _objs_libxmhfhw
LIBXMHFHW_VERIF_DIR = _verif_libxmhfhw

THE_ARCHIVE = libxmhfhw.a

LLC_ATTR = -3dnow,-3dnowa,-64bit,-64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop

# targets
.PHONY: verify
verify:
	mkdir -p $(LIBXMHFHW_VERIF_DIR)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_fls.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_fls.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/verify/<something.c> xmhfhw_cpu_fls.cS.c $(V_XMHFHWM_MODULES)
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main sha1 -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) xmhfhw_cpu_fls.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main fls -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_fls.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main __getsec_capabilities -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getseccaps.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main __getsec_parameters -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getsecparams.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main __getsec_senter -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getsecsenter.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main __getsec_sexit -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getsecsexit.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main __getsec_smctrl -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getsecsmctrl.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main __getsec_wakeup -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getsecwakeup.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_getcpuvendor -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_getvendor.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_x86_cpuhasxsavefeature -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_hasxsave.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main set_all_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_mtrrenabledisable.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_cpu_x86_restore_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_mtrrrestore.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_cpu_x86_save_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_mtrrsave.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main set_mem_type -lib-entry -wp -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_mtrrsetmemtype.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main validate_mtrrs -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_mtrrvalidate.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_bios_data_size -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetbiosdatasize.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_bios_data_start -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetbiosdatastart.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_txt_heap -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetheap.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_os_mle_data_size -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetosmledatasize.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_os_mle_data_start -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetosmledatastart.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_os_sinit_data_size -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetossinitdatasize.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_os_sinit_data_start -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetossinitdatastart.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_sinit_mle_data_size -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetsinitmledatasize.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main get_sinit_mle_data_start -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtgetsinitmledatastart.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main txt_is_launched -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtislaunched.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main read_priv_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtreadprivcr.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main read_pub_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtreadpubcr.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main write_priv_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtwriteprivcr.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main write_pub_config_reg -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_cpu_txtwritepubcr.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_x86_reboot -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_keyb_reboot.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_x86_getcpulapicid -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_lapic_getid.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_lapic_isbsp -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_lapic_isbsp.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_bus_init -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_pci_initbus.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_x86_pci_type1_read -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_pci_read.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_x86_pci_type1_write -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_pci_write.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhf_baseplatform_arch_x86_udelay -lib-entry -wp -wp-rte -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_pit_udelay.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_acpi_getRSDP -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_sysmem_getacpirsdp.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main _vtd_reg_read -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_readreg.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main _vtd_reg_write -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_writereg.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_disable_pmr -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_disablepmr.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_disable_translation -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_disabletrans.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_enable_translation -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_enabletrans.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_initialize -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_initdrhd.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_invlcaches.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_set_phm_base_and_limit -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_setphm.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_set_plm_base_and_limit -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_setplm.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -main xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table -lib-entry -wp -wp-rte -wp-model +cint+cast -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/xmhfhw_vtd_setret.c
	$(CP) -f $(srcdir)/../libxmhfgeec/xmhfgeec_slabmapdef.c $(LIBXMHFHW_VERIF_DIR)/xmhfgeec_slabmapdef.c
	#$(CP) -f $(srcdir)/xmhfhw_cpu_bsrl.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_bsrl.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_bsrl.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_cpuid.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_cpuid.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_cpuid.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_disableintr.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_disableintr.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_disableintr.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_enableintr.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_enableintr.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_enableintr.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_getgdtbase.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_getgdtbase.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_getgdtbase.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_getidtbase.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_getidtbase.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_getidtbase.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_getsec.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_getsec.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_getsec.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_gettssbase.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_gettssbase.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_gettssbase.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_inb.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_inb.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_inb.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_inl.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_inl.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_inl.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_invept.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_invept.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_invept.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_invvpid.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_invvpid.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_invvpid.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_inw.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_inw.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_inw.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_loadgdt.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_loadgdt.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_loadgdt.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_loadidt.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_loadidt.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_loadidt.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_loadtr.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_loadtr.cS.c
	#$(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_loadtr.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_outb.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_outb.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_outb.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_outl.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_outl.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_outl.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_outw.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_outw.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_outw.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	#$(CP) -f $(srcdir)/xmhfhw_cpu_pause.cS $(LIBXMHFHW_VERIF_DIR)/xmhfhw_cpu_pause.cS.c
	#cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c xmhfhw_cpu_pause.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	@for i in $(CS_SOURCES); \
	do \
		(cp -f $(srcdir)/$$i $(LIBXMHFHW_VERIF_DIR)/$$i.c) || exit 1; \
	done;
	@echo Sources prepped.
	cd $(LIBXMHFHW_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__XXX__ $(VFLAGS) $(srcdir)/verify/xmhfhw_casmfuncs_driver.c *.c $(V_XMHFHWM_MODULES)


.PHONY: all
all: $(THE_ARCHIVE)
#all:

$(THE_ARCHIVE): $(OBJECTS)
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	cd $(LIBXMHFHW_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	cp $(LIBXMHFHW_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(LIBXMHFHW_OBJECTS_DIR)/$@ $<
	#$(CC) -fomit-frame-pointer -O2 -S -emit-llvm $(CFLAGS) $< -o $(LIBXMHFHW_OBJECTS_DIR)/$(@F).ll
	#cd $(LIBXMHFHW_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	#cd $(LIBXMHFHW_OBJECTS_DIR) && llc -O=2 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	#cd $(LIBXMHFHW_OBJECTS_DIR) && $(CC) -O2 -c $(CFLAGS) $(@F).s -o $(@F)

%.o: %.cS
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	cp -f $< $(LIBXMHFHW_OBJECTS_DIR)/$(@F).c
	cd $(LIBXMHFHW_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_FLAGS) -O0 $(@F).c
	#cd $(LIBXMHFHW_OBJECTS_DIR) && $(XMHF_DIR)/tools/extractasm.pl $(@F).mach > $(@F).S
	cd $(LIBXMHFHW_OBJECTS_DIR) && frama-c -load-script $(XMHF_DIR)/tools/ucasm.ml -ucasm-infile $(@F).mach -ucasm-outfile $(@F).S
	cd $(LIBXMHFHW_OBJECTS_DIR) && gcc -c $(ASFLAGS) -o $@ $(@F).S
	#cd $(LIBXMHFHW_OBJECTS_DIR) && mv $(@F).o $@



#%.o: %.cS
#	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
#	@echo Building "$@" from "$<"
#	cp -f $< $(LIBXMHFHW_OBJECTS_DIR)/$(@F).c
#	$(CC) -fomit-frame-pointer -O2 -S -emit-llvm $(CFLAGS) $(LIBXMHFHW_OBJECTS_DIR)/$(@F).c -o $(LIBXMHFHW_OBJECTS_DIR)/$(@F).ll
#	cd $(LIBXMHFHW_OBJECTS_DIR) && fixnaked.pl $(@F).ll
#	cd $(LIBXMHFHW_OBJECTS_DIR) && llc -O=2 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
#	cd $(LIBXMHFHW_OBJECTS_DIR) && $(CC) -O2 -c $(CFLAGS) $(@F).s -o $(@F)


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFHW_OBJECTS_DIR)

