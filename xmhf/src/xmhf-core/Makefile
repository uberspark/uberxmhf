# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)


#-----build rules
.PHONY: all
all: components runtime sl init hypervisor-$(TARGET_HWPLATFORM).bin.gz

.PHONY: components
components:
	#EMHF memory protection component
	cd components/xmhf-memprot && $(MAKE) -w all
	#EMHF partition event-hub component
	cd components/xmhf-parteventhub && $(MAKE) -w all
	#EMHF SMP guest component
	cd components/xmhf-smpguest && $(MAKE) -w all
	#EMHF DMA protection component
	cd components/xmhf-dmaprot && $(MAKE) -w all
	#EMHF exception handler component
	cd components/xmhf-xcphandler && $(MAKE) -w all
	#EMHF base platform component
	cd components/xmhf-baseplatform && $(MAKE) -w all
	#EMHF partition component
	cd components/xmhf-partition && $(MAKE) -w all
	#EMHF TPM component
	cd components/xmhf-tpm && $(MAKE) -w all
	#EMHF debug component
	cd components/xmhf-debug && $(MAKE) -w all
	#EMHF libemhfc environment callbacks
	cd components/xmhf-xmhfcbackend && $(MAKE) -w all

.PHONY: runtime
runtime: 
	#EMHF runtime component
	cd components/xmhf-runtime && $(MAKE) -w all

.PHONY: sl
sl: runtime 
	#EMHF secure loader component
	# Double-dollar-sign required to cause make to provide literal dollar sign to perl
	# Objective: Create an escaped ASCII string containing the SHA-1 hash of the
	# runtime and pass it to the SL's makefile
	cd components/xmhf-sl && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

.PHONY: init
init: sl runtime 
	#make init	
	cd init && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLBELOW64K_INTEGRITY_HASH=\""$(shell ( dd if=./components/xmhf-sl/sl.bin bs=1024 count=64 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLABOVE64K_INTEGRITY_HASH=\""$(shell ( dd if=./components/xmhf-sl/sl.bin bs=1024 skip=64 count=1984 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

sl/sl.bin: sl
runtime/runtime.bin: runtime
hypervisor-$(TARGET_HWPLATFORM).bin.gz: components/xmhf-sl/sl.bin components/xmhf-runtime/runtime.bin init/init-$(TARGET_HWPLATFORM).bin
	# concatenate sl image and runtime image 
	$(CAT) ./components/xmhf-sl/sl.bin ./components/xmhf-runtime/runtime.bin > ./hypervisor.tmp.img
	gzip -c ./hypervisor.tmp.img > ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf ./hypervisor.tmp.img 
	# install loader and runtime images to INSTALLDIR
	$(CP) ./init/init-$(TARGET_HWPLATFORM).bin $(HYPOUTDIR)/init-$(TARGET_HWPLATFORM).bin
	$(CP) ./hypervisor-$(TARGET_HWPLATFORM).bin.gz $(HYPOUTDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz

# late initialization support
.PHONY: init-late
init-late: hypervisor-$(TARGET_HWPLATFORM).bin.gz
	#make late initialization, currently defaults to linux os support
	cd ./init-late/os/linux && $(MAKE)
	#TODO: needs OS selection via configuration option
	$(CP) ./init-late/os/linux/emhfil.ko $(HYPOUTDIR)/emhfil.ko
	$(CP) ./init-late/os/linux/emhfil.sh $(HYPOUTDIR)/emhfil.sh


# cleanup rules
.PHONY: clean init-late-clean
clean: 
	cd components/xmhf-memprot && $(MAKE) -w clean
	cd components/xmhf-parteventhub && $(MAKE) -w clean
	cd components/xmhf-dmaprot && $(MAKE) -w clean
	cd components/xmhf-smpguest && $(MAKE) -w clean
	cd components/xmhf-xcphandler && $(MAKE) -w clean
	cd components/xmhf-baseplatform && $(MAKE) -w clean
	cd components/xmhf-partition && $(MAKE) -w clean
	cd components/xmhf-tpm && $(MAKE) -w clean
	cd components/xmhf-debug && $(MAKE) -w clean
	cd components/xmhf-xmhfcbackend && $(MAKE) -w clean

	cd components/xmhf-runtime && $(MAKE) -w clean

	cd components/xmhf-sl && $(MAKE) -w clean
	
	cd init && $(MAKE) -w clean

	rm -rf $(APPOBJECTSDIR)

	rm -rf ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf $(HYPOUTDIR)/init-$(TARGET_HWPLATFORM).bin
	$(RM) -rf $(HYPOUTDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz

init-late-clean:
	cd ./init-late/os/linux && $(MAKE) clean
	$(RM) -rf $(HYPOUTDIR)/emhfil.ko
	$(RM) -rf $(HYPOUTDIR)/emhfil.sh


.PHONY: install-dev
install-dev:
	# Nothing to do here

	
