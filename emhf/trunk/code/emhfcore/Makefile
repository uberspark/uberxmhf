# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)


#-----build rules
.PHONY: all
all: components runtime sl init hypervisor-$(TARGET_HWPLATFORM).bin.gz

.PHONY: components
components:
	#EMHF memory protection component
	cd components/emhf-memprot && $(MAKE) -w all
	#EMHF partition event-hub component
	cd components/emhf-parteventhub && $(MAKE) -w all
	#EMHF SMP guest component
	cd components/emhf-smpguest && $(MAKE) -w all
	#EMHF DMA protection component
	cd components/emhf-dmaprot && $(MAKE) -w all
	#EMHF exception handler component
	cd components/emhf-xcphandler && $(MAKE) -w all
	#EMHF base platform component
	cd components/emhf-baseplatform && $(MAKE) -w all
	#EMHF partition component
	cd components/emhf-partition && $(MAKE) -w all
	#EMHF TPM component
	cd components/emhf-tpm && $(MAKE) -w all
	#EMHF debug component
	cd components/emhf-debug && $(MAKE) -w all
	#EMHF libemhfc environment callbacks
	cd components/emhf-emhfcbackend && $(MAKE) -w all

.PHONY: runtime
runtime: 
	#EMHF runtime component
	cd components/emhf-runtime && $(MAKE) -w all

.PHONY: sl
sl: runtime 
	#EMHF secure loader component
	# Double-dollar-sign required to cause make to provide literal dollar sign to perl
	# Objective: Create an escaped ASCII string containing the SHA-1 hash of the
	# runtime and pass it to the SL's makefile
	cd components/emhf-sl && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/emhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

.PHONY: init
init: sl runtime 
	#make init	
	cd init && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/emhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLBELOW64K_INTEGRITY_HASH=\""$(shell ( dd if=./components/emhf-sl/sl.bin bs=1024 count=64 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLABOVE64K_INTEGRITY_HASH=\""$(shell ( dd if=./components/emhf-sl/sl.bin bs=1024 skip=64 count=1984 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

sl/sl.bin: sl
runtime/runtime.bin: runtime
hypervisor-$(TARGET_HWPLATFORM).bin.gz: components/emhf-sl/sl.bin components/emhf-runtime/runtime.bin init/init-$(TARGET_HWPLATFORM).bin
	# concatenate sl image and runtime image 
	$(CAT) ./components/emhf-sl/sl.bin ./components/emhf-runtime/runtime.bin > ./hypervisor.tmp.img
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
	cd components/emhf-memprot && $(MAKE) -w clean
	cd components/emhf-parteventhub && $(MAKE) -w clean
	cd components/emhf-dmaprot && $(MAKE) -w clean
	cd components/emhf-smpguest && $(MAKE) -w clean
	cd components/emhf-xcphandler && $(MAKE) -w clean
	cd components/emhf-baseplatform && $(MAKE) -w clean
	cd components/emhf-partition && $(MAKE) -w clean
	cd components/emhf-tpm && $(MAKE) -w clean
	cd components/emhf-debug && $(MAKE) -w clean
	cd components/emhf-emhfcbackend && $(MAKE) -w clean

	cd components/emhf-runtime && $(MAKE) -w clean

	cd components/emhf-sl && $(MAKE) -w clean
	
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

	
