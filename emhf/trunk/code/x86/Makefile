# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)

#-----build rules
.PHONY: all
all: common runtime sl init

common:
	#make libcommon first	
	cd libcommon && $(MAKE) -w all

runtime: common
	#make runtime
	cd runtime && $(MAKE) -w all

sl: runtime common
	#make sl
	# Double-dollar-sign required to cause make to provide literal dollar sign to perl
	# Objective: Create an escaped ASCII string containing the SHA-1 hash of the
	# runtime and pass it to the SL's makefile
	cd sl && $(MAKE) -w all RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

init: sl runtime common
	#make init	
	cd init && $(MAKE) -w all

	# concatenate sl image and runtime image 
	$(CAT) ./sl/sl.bin ./runtime/runtime.bin > ./hypervisor.tmp.img
	dd if=./hypervisor.tmp.img of=hypervisor.tmp-64K.img bs=1024 count=64
	dd if=./hypervisor.tmp.img of=hypervisor.tmp-128K.img bs=1024 count=128
	sha1sum hypervisor.tmp-64K.img
	sha1sum hypervisor.tmp-128K.img
	sha1sum hypervisor.tmp.img
	gzip -c ./hypervisor.tmp.img > ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf ./hypervisor.tmp.img 

# cleanup rules
.PHONY: clean 
clean: 
	cd runtime && $(MAKE) -w clean
	cd sl && $(MAKE) -w clean
	cd init && $(MAKE) -w clean
	cd libcommon && $(MAKE) -w clean
	
