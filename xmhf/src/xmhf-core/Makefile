# top-level makefile for XMHF x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)


#-----build rules
.PHONY: all
all: runtime 

.PHONY: runtime
runtime:
	cd xmhf-runtime && $(MAKE) -w all

.PHONY: secureloader
secureloader: runtime 
	# Double-dollar-sign required to cause make to provide literal dollar sign to perl
	# Objective: Create an escaped ASCII string containing the SHA-1 hash of the
	# runtime and pass it to the SL's makefile
	cd xmhf-secureloader && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

.PHONY: bootloader
bootloader: secureloader runtime 
	cd xmhf-bootloader && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLBELOW64K_INTEGRITY_HASH=\""$(shell ( dd if=./xmhf-secureloader/sl.bin bs=1024 count=64 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLABOVE64K_INTEGRITY_HASH=\""$(shell ( dd if=./xmhf-secureloader/sl.bin bs=1024 skip=64 count=1984 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

secureloader/sl.bin: secureloader
runtime/runtime.bin: runtime
hypervisor-$(TARGET_HWPLATFORM).bin.gz: xmhf-secureloader/sl.bin xmhf-runtime/xmhf-startup/runtime.bin xmhf-bootloader/init-$(TARGET_HWPLATFORM).bin
	# concatenate sl image and runtime image 
	$(CAT) ./xmhf-secureloader/sl.bin ./xmhf-runtime/xmhf-startup/runtime.bin > ./hypervisor.tmp.img
	gzip -c ./hypervisor.tmp.img > ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf ./hypervisor.tmp.img 
	# install loader and runtime images to INSTALLDIR
	$(CP) ./xmhf-bootloader/init-$(TARGET_HWPLATFORM).bin $(HYPOUTDIR)/init-$(TARGET_HWPLATFORM).bin
	$(CP) ./hypervisor-$(TARGET_HWPLATFORM).bin.gz $(HYPOUTDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz


# cleanup rules
#.PHONY: clean init-late-clean
.PHONY: clean 
clean: 
	cd xmhf-runtime && $(MAKE) -w clean

	cd xmhf-secureloader && $(MAKE) -w clean
	
	cd xmhf-bootloader && $(MAKE) -w clean

	rm -rf $(APPOBJECTSDIR)

	rm -rf ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf $(HYPOUTDIR)/init-$(TARGET_HWPLATFORM).bin
	$(RM) -rf $(HYPOUTDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz


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
