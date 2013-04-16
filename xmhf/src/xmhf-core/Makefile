# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)


#-----build rules
.PHONY: all
all: runtime secureloader bootloader hypervisor-$(TARGET_HWPLATFORM).bin.gz

.PHONY: runtime
runtime:
	#EMHF memory protection component
	cd xmhf-runtime/xmhf-memprot && $(MAKE) -w all
	#EMHF partition event-hub component
	cd xmhf-runtime/xmhf-parteventhub && $(MAKE) -w all
	#EMHF SMP guest component
	cd xmhf-runtime/xmhf-smpguest && $(MAKE) -w all
	#EMHF DMA protection component
	cd xmhf-runtime/xmhf-dmaprot && $(MAKE) -w all
	#EMHF exception handler component
	cd xmhf-runtime/xmhf-xcphandler && $(MAKE) -w all
	#EMHF base platform component
	cd xmhf-runtime/xmhf-baseplatform && $(MAKE) -w all
	#EMHF partition component
	cd xmhf-runtime/xmhf-partition && $(MAKE) -w all
	#EMHF TPM component
	cd xmhf-runtime/xmhf-tpm && $(MAKE) -w all
	#EMHF debug component
	cd xmhf-runtime/xmhf-debug && $(MAKE) -w all
	#EMHF libemhfc environment callbacks
	cd xmhf-runtime/xmhf-xmhfcbackend && $(MAKE) -w all
	#EMHF runtime component
	cd xmhf-runtime/xmhf-runtime && $(MAKE) -w all

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
hypervisor-$(TARGET_HWPLATFORM).bin.gz: xmhf-secureloader/sl.bin xmhf-runtime/xmhf-runtime/runtime.bin xmhf-bootloader/init-$(TARGET_HWPLATFORM).bin
	# concatenate sl image and runtime image 
	$(CAT) ./xmhf-secureloader/sl.bin ./xmhf-runtime/xmhf-runtime/runtime.bin > ./hypervisor.tmp.img
	gzip -c ./hypervisor.tmp.img > ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf ./hypervisor.tmp.img 
	# install loader and runtime images to INSTALLDIR
	$(CP) ./xmhf-bootloader/init-$(TARGET_HWPLATFORM).bin $(HYPOUTDIR)/init-$(TARGET_HWPLATFORM).bin
	$(CP) ./hypervisor-$(TARGET_HWPLATFORM).bin.gz $(HYPOUTDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz

# late initialization support
#.PHONY: init-late
#init-late: hypervisor-$(TARGET_HWPLATFORM).bin.gz
#	#make late initialization, currently defaults to linux os support
#	cd ./init-late/os/linux && $(MAKE)
#	#TODO: needs OS selection via configuration option
#	$(CP) ./init-late/os/linux/emhfil.ko $(HYPOUTDIR)/emhfil.ko
#	$(CP) ./init-late/os/linux/emhfil.sh $(HYPOUTDIR)/emhfil.sh


# cleanup rules
#.PHONY: clean init-late-clean
.PHONY: clean 
clean: 
	cd xmhf-runtime/xmhf-memprot && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-parteventhub && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-dmaprot && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-smpguest && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-xcphandler && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-baseplatform && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-partition && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-tpm && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-debug && $(MAKE) -w clean
	cd xmhf-runtime/xmhf-xmhfcbackend && $(MAKE) -w clean

	cd xmhf-runtime/xmhf-runtime && $(MAKE) -w clean

	cd xmhf-secureloader && $(MAKE) -w clean
	
	cd xmhf-bootloader && $(MAKE) -w clean

	rm -rf $(APPOBJECTSDIR)

	rm -rf ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf $(HYPOUTDIR)/init-$(TARGET_HWPLATFORM).bin
	$(RM) -rf $(HYPOUTDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz

#init-late-clean:
#	cd ./init-late/os/linux && $(MAKE) clean
#	$(RM) -rf $(HYPOUTDIR)/emhfil.ko
#	$(RM) -rf $(HYPOUTDIR)/emhfil.sh


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
