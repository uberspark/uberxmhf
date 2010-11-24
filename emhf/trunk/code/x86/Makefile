# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)

#-----build rules
.PHONY: all
all: 
  
	#make libcommon first	
	cd libcommon && $(MAKE) -w all

	#make init	
	cd init && $(MAKE) -w all

	#make sl
	cd sl && $(MAKE) -w all

	#make runtime
	cd runtime && $(MAKE) -w all

	# concatenate sl image and runtime image 
	$(CAT) $(EMHFCOREDIR)/sl/sl.bin $(EMHFCOREDIR)/runtime/runtime.bin > $(EMHFCOREDIR)/hypervisor.tmp.img
	gzip -c $(EMHFCOREDIR)/hypervisor.tmp.img > $(EMHFCOREDIR)/hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf $(EMHFCOREDIR)/hypervisor.tmp.img 

# cleanup rules
.PHONY: clean 
clean: 
	cd runtime && $(MAKE) -w clean
	cd sl && $(MAKE) -w clean
	cd init && $(MAKE) -w clean
	cd libcommon && $(MAKE) -w clean
	
