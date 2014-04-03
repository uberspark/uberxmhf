# top-level makefile for XMHF x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree build)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

# export XMHFCORE_OBJECTS_DIR = _objs_xmhf-core

#-----build rules
.PHONY: all
all: 
	mkdir -p $(XMHFCORE_OBJECTS_DIR)
	#@echo --------------------------------------------------------------
	#@echo building libxmhfcore...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFCORE_SRC)/Makefile -w all
	#@echo libxmhfcore.a build SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo building libxmhfhw...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFHW_SRC)/Makefile -w all
	#@echo libxmhfhw.a build SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo building libbaremetal-xmhfbackends...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBBAREMETAL_XMHFBACKENDS_SRC)/Makefile -w all
	#@echo libbaremetal-xmhfbackends.a build SUCCESS
	#@echo building libxmhfdebug...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFDEBUG_SRC)/Makefile -w all
	#@echo libbaremetal-xmhfbackends.a build SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo building runtime...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_RUNTIME_SRC)/Makefile -w all
	#@echo runtime build SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo building xmhf-secureloader...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_SECURELOADER_SRC)/Makefile -w all \
	#		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"
	#@echo xmhf-secureloader build SUCCESS
	#@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo building xmhf-bootloader...
	cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_BOOTLOADER_SRC)/Makefile -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLBELOW64K_INTEGRITY_HASH=\""$(shell ( dd if=$(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-secureloader/sl.bin bs=1024 count=64 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLABOVE64K_INTEGRITY_HASH=\""$(shell ( dd if=$(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-secureloader/sl.bin bs=1024 skip=64 count=1984 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"
	@echo xmhf-bootloader build SUCCESS
	@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo generating final binaries...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(CAT) ./_objs_xmhf-bootloader/xmhf-bootloader.bin ./_objs_xmhf-secureloader/xmhf-secureloader.bin $(XMHF_OBJDIR)/_objs_xmhf-runtime/xmhf-runtime.bin > ./xmhf.tmp.img
	#cd $(XMHFCORE_OBJECTS_DIR) && gzip -c ./xmhf.tmp.img > ./xmhf-$(TARGET_HWPLATFORM).bin.gz
	#cd $(XMHFCORE_OBJECTS_DIR) && $(RM) -rf ./xmhf.tmp.img 
	#@echo xmhf binary generation SUCCESS
	#@echo --------------------------------------------------------------

# cleanup rules
#.PHONY: clean init-late-clean
.PHONY: clean 
clean: 
	mkdir -p $(XMHFCORE_OBJECTS_DIR)
	#@echo --------------------------------------------------------------
	#@echo cleaning libxmhfcore...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFCORE_SRC)/Makefile -w clean
	#@echo libxmhfcore.a cleanup SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo cleaning libxmhfhw...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFHW_SRC)/Makefile -w clean
	#@echo libxmhfhw.a cleanup SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo cleaning libbaremetal-xmhfbackends...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBBAREMETAL_XMHFBACKENDS_SRC)/Makefile -w clean
	#@echo libbaremetal-xmhfbackends.a cleanup SUCCESS
	#@echo cleaning libxmhfdebug...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFDEBUG_SRC)/Makefile -w clean
	#@echo libxmhfdebug.a cleanup SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo cleaning runtime...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_RUNTIME_SRC)/Makefile -w clean
	#@echo runtime cleanup SUCCESS
	#@echo --------------------------------------------------------------
	#@echo --------------------------------------------------------------
	#@echo cleaning xmhf-secureloader...
	#cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_SECURELOADER_SRC)/Makefile -w clean
	#@echo xmhf-secureloader cleanup SUCCESS
	#@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo cleaning xmhf-bootloader...
	cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_BOOTLOADER_SRC)/Makefile -w clean
	@echo xmhf-bootloader cleanup SUCCESS
	@echo --------------------------------------------------------------
	$(RM) -rf $(XMHFCORE_OBJECTS_DIR)

.PHONY: install-dev
install-dev:
	# Nothing to do here

.PHONY: verify
verify:
	#cd verification/ && $(MAKE) -w verify
	mkdir -p $(XMHFCORE_OBJECTS_DIR)
	@echo --------------------------------------------------------------
	@echo preparing libbaremetal-xmhfbackends...
	cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBBAREMETAL_XMHFBACKENDS_SRC)/Makefile -w verify
	@echo libbaremetal-xmhfbackends prepared
	@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo preparing libxmhfhw...
	cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(LIBXMHFHW_SRC)/Makefile -w verify
	@echo libxmhfhw prepared
	@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo preparing xmhf-secureloader...
	cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_SECURELOADER_SRC)/Makefile -w verify
	@echo xmhf-secureloader prepared
	@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo preparing xmhf-runtime...
	cd $(XMHFCORE_OBJECTS_DIR) && $(MAKE) -f $(XMHF_RUNTIME_SRC)/Makefile -w verify
	@echo xmhf-runtime prepared
	@echo --------------------------------------------------------------
	#cbmc --ILP32 --little-endian --i386-linux -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ $(VFLAGS) $(srcdir)/verification/xmhf-core-verify-sl.c $(XMHFCORE_OBJECTS_DIR)/_objs_libbaremetal-xmhfbackends/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_libxmhfhw/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-secureloader/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-secureloader/_objs_libxmhfslarch/*.v.c
	#cbmc --ILP32 --little-endian --i386-linux -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ $(VFLAGS) $(srcdir)/verification/xmhf-core-verify-startup.c $(XMHFCORE_OBJECTS_DIR)/_objs_libbaremetal-xmhfbackends/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_libxmhfhw/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/_objs_libxmhfruntimearch/*.v.c
	cbmc --ILP32 --little-endian --i386-linux -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ $(VFLAGS) $(srcdir)/verification/xmhf-core-verify-eventhub.c $(XMHFCORE_OBJECTS_DIR)/_objs_libbaremetal-xmhfbackends/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_libxmhfhw/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/_objs_libxmhfruntimearch/*.v.c
.PHONY: verifyinit
verifyinit:
	cd verification/ && $(MAKE) -w verifyinit

.PHONY: verifyall
verifyall:
	cd verification/ && $(MAKE) -w verifyall

.PHONY: verifysafeupd
verifysafeupd:
	cd verification/ && $(MAKE) -w verifysafeupd
