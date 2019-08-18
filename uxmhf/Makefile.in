######
# top-level Makefile for XMHF
# author: amit vasudevan (amitvasudevan@acm.org)
######

include ./uxmhf-common.mk



######
# uXMHF build variables
######

## bootloader source path
export XMHF_BOOTLOADER_SRC := $(realpath $(XMHF_DIR)/xmhf-bootloader)


## uobj source paths and count
#export XMHF_SLAB_DIRS := $(shell awk -F, '{print $$1}' $(XMHF_DIR)/xmhf-uobjs/UOBJLIST)
export XMHF_SLAB_DIRS := $(shell sed '1,2d;$$d' $(XMHF_DIR)/xmhf-uobjs/UOBJLIST | sed '$$d' | awk '{$$1=$$1;print}')
XMHF_SLAB_NAMES := $(notdir $(XMHF_SLAB_DIRS))
export XMHF_SLAB_TOTAL := $(shell sed '1,2d;$$d' $(XMHF_DIR)/xmhf-uobjs/UOBJLIST | sed '$$d' | awk '{$$1=$$1;print}' | wc -l)



######
# top-level build targets
######


######
# uxmhf image
.PHONY: uxmhf-image
uxmhf-image: uxmhf-uobjsbuild uxmhf-bootloader uxmhf-binimage






######
# uxmhf uobj manifest/infotable related build harness


.PHONY: _uobjs_preprocessmanifests
_uobjs_preprocessmanifests:
	mkdir -p $(XMHF_OBJDIR)
	@for i in $(XMHF_SLAB_NAMES); \
	do \
		(cd $(XMHF_OBJDIR) && echo "Prepping uobj manifest for $$i..." && $(CP) -f $(XMHF_DIR)/xmhf-uobjs/$$i/$$i.gsm $$i.gsm.c && $(CCERT) -E $(CCERT_CFLAGS) -D__ASSEMBLY__ $$i.gsm.c >$(XMHF_DIR)/xmhf-uobjs/$$i/$$i.gsm.pp) || exit 1; \
	done;
	@echo uobj manifests prepped

.PHONY: _uobjs_configureandgenerateuobjinfo
_uobjs_configureandgenerateuobjinfo:
	$(MKDIR) -p $(XMHF_OBJDIR)
	cd $(XMHF_DIR) && $(USPARK_INSTALL_TOOLSDIR)/umf $(XMHF_DIR)/xmhf-uobjs/UOBJLIST $(XMHF_DIR)/configure-uxmhfuobj $(XMHF_OBJDIR)/uobjinfotable.c $(XMHF_OBJDIR)/xmhf.lscript $(XMHF_CONFIG_LOADADDR) $(XMHF_CONFIG_LOADMAXSIZE) $(XMHFGEEC_TOTAL_UHSLABS) $(XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES) $(XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES) $(XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES) 0 "$(CCERT_CFLAGS)"


.PHONY: uobjinfotable_build
uobjinfotable_build:
	@echo building uobjinfotable...
	$(MKDIR) -p $(XMHF_OBJDIR)
	cd $(XMHF_OBJDIR) && $(CCERT) -c $(CCERT_CFLAGS) -o $(XMHF_OBJDIR)/uobjinfotable.o uobjinfotable.c
	@echo uobjinfotable built sucessfully.
	
	
######
# uxmhf uobj build
	
.PHONY: uxmhf-uobjsbuild
uxmhf-uobjsbuild: _uobjs_configureandgenerateuobjinfo uobjinfotable_build
	@echo Building uobjs...
	@for i in $(XMHF_SLAB_DIRS); \
	do \
		(cd $(XMHF_OBJDIR) &&	echo "Making all in $$i..." && $(MAKE) -f $(XMHF_DIR)/xmhf-uobjs/$$i/Makefile -w all) || exit 1; \
	done;
	@echo uobjs build SUCCESS




######
# uxmhf bootloader
.PHONY: uxmhf-bootloader
uxmhf-bootloader:  
	@echo Building XMHF boot loader...
	cd $(XMHF_OBJDIR) && $(MAKE) -f $(XMHF_BOOTLOADER_SRC)/Makefile -w all
	@echo XMHF boot loader build SUCCESS



######
# uxmhf binary image
.PHONY: uxmhf-binimage
uxmhf-binimage:
	@echo Generating uXMHF binary image...
	cd $(XMHF_OBJDIR) && $(CP) -f xmhf.lscript xmhf.lscript.c
	cd $(XMHF_OBJDIR) && $(CC) $(ASMFLAGS) -P -E xmhf.lscript.c -o xmhf.lds
	cd $(XMHF_OBJDIR) && $(LD) --oformat elf32-i386 -T xmhf.lds -o xmhf.exe 
	cd $(XMHF_OBJDIR) && $(OBJCOPY) --output-format=binary xmhf.exe xmhf.bin
	cd $(XMHF_OBJDIR) && $(CAT) ./_objs_xmhf-bootloader/xmhf-bootloader.bin ./xmhf.bin > ./xmhf.tmp.img
	cd $(XMHF_OBJDIR) && gzip -c ./xmhf.tmp.img > ./xmhf-$(XMHF_TARGET_TRIAD).bin.gz
	cd $(XMHF_OBJDIR) && $(RM) -rf ./xmhf.tmp.img
	@echo uXMHF binary image generation SUCCESS


	
######
# uxmhf verify targets

.PHONY: uxmhf-verif-gensentinelstubs
uxmhf-verif-gensentinelstubs: _uobjs_configureandgenerateuobjinfo
		@echo Proceeding to generate sentinel stubs for blueprint conformance...
		$(MKDIR) -p $(XMHF_OBJDIR)/_verif_bp
		cd $(XMHF_DIR) && $(USPARK_INSTALL_TOOLSDIR)/ubp $(XMHF_DIR)/xmhf-uobjs/UOBJLIST $(XMHF_OBJDIR)/_verif_bp/ $(XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES) $(XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES) $(XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES) 0
		@echo sentinel stubs generated

	

	
.PHONY: uxmhf-verifyuobjs-prep
uxmhf-verifyuobjs-prep: _uobjs_configureandgenerateuobjinfo uxmhf-verif-gensentinelstubs


.PHONY: uxmhf-verifyuobjs-all
uxmhf-verifyuobjs-all: uxmhf-verifyuobjs-prep 
	@for i in $(XMHF_SLAB_NAMES); \
	do \
		(cd $(XMHF_DIR)/xmhf-uobjs/$$i && echo "Verifying uobj $$i..." && $(MAKE) -w verify) || exit 1; \
	done;
	@echo All uobjs verified!

	
######
# uxmhf cleanup targets
	
.PHONY: clean 
clean:
	$(RM) -rf $(XMHF_OBJDIR)

# http://www.gnu.org/software/automake/manual/automake.html#Clean
distclean: clean
	$(RM) config.log config.status
	$(RM) -rf Makefile


	
	
######
# uxmhf autoconf targets

Makefile: Makefile.in config.status
	./config.status $@

config.status: configure
	./config.status --recheck

configure: configure.ac
	autoconf --output=configure configure.ac

