# top-level makefile for XMHF x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)

# e.g. init-x86-i386.bin or init-x86-amd64.bin
INIT_BIN := init-$(TARGET_HWPLATFORM)-$(TARGET_SUBARCH).bin

# e.g. hypervisor-x86-i386.bin.gz or hypervisor-x86-amd64.bin.gz
HYPERVISOR_BIN_GZ := hypervisor-$(TARGET_HWPLATFORM)-$(TARGET_SUBARCH).bin.gz

#-----build rules
.PHONY: all
all: runtime secureloader bootloader $(HYPERVISOR_BIN_GZ)

.PHONY: runtime
runtime:
	cd xmhf-runtime && $(MAKE) -w all

.PHONY: secureloader
secureloader: runtime 
	# Double-dollar-sign required to cause make to provide literal dollar sign to perl
	# Objective: Create an escaped ASCII string containing the SHA-1 hash of the
	# runtime and pass it to the SL's makefile
	cd xmhf-secureloader && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ./xmhf-runtime/runtime.sha1 ))"\"

.PHONY: bootloader
bootloader: secureloader runtime 
	cd xmhf-bootloader && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ./xmhf-runtime/runtime.sha1 ))"\" \
		SLBELOW64K_INTEGRITY_HASH=\""$(shell ( perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ./xmhf-secureloader/sl-below.sha1 ))"\" \
		SLABOVE64K_INTEGRITY_HASH=\""$(shell ( perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ./xmhf-secureloader/sl-above.sha1 ))"\"

xmhf-bootloader/$(INIT_BIN): bootloader

xmhf-secureloader/sl.bin: secureloader
xmhf-runtime/runtime.bin: runtime
$(HYPERVISOR_BIN_GZ): xmhf-secureloader/sl.bin xmhf-runtime/runtime.bin xmhf-bootloader/$(INIT_BIN)
	# concatenate sl image and runtime image 
	$(CAT) ./xmhf-secureloader/sl.bin ./xmhf-runtime/runtime.bin > ./hypervisor.tmp.img
	gzip -c ./hypervisor.tmp.img > $(HYPERVISOR_BIN_GZ)
	$(RM) -rf ./hypervisor.tmp.img 
	# install loader and runtime images to INSTALLDIR
	$(CP) ./xmhf-bootloader/$(INIT_BIN) $(HYPOUTDIR)/$(INIT_BIN)
	$(CP) $(HYPERVISOR_BIN_GZ) $(HYPOUTDIR)/$(HYPERVISOR_BIN_GZ)


# cleanup rules
#.PHONY: clean init-late-clean
.PHONY: clean 
clean: 
	cd xmhf-runtime && $(MAKE) -w clean

	cd xmhf-secureloader && $(MAKE) -w clean
	
	cd xmhf-bootloader && $(MAKE) -w clean

	rm -rf $(APPOBJECTSDIR)

	rm -rf ./$(HYPERVISOR_BIN_GZ)
	$(RM) -rf $(HYPOUTDIR)/$(INIT_BIN)
	$(RM) -rf $(HYPOUTDIR)/$(HYPERVISOR_BIN_GZ)


.PHONY: install-dev
install-dev:
	# Nothing to do here

.PHONY: verify
verify:
	cd verification/ && $(MAKE) -w verify
	
.PHONY: verifyinit
verifyinit:
	cd verification/ && $(MAKE) -w verifyinit

.PHONY: verifyall
verifyall:
	cd verification/ && $(MAKE) -w verifyall
