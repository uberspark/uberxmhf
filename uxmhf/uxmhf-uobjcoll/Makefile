#   uxmhf Makefile refactored to use the überSpark next-gen toolkit
#   
#   author: ethan joseph <ethanj217@gmail.com>
#

.PHONY: all
all:
	@echo building uxmhf collection...
	uberspark staging switch uxmhf-pc 
	uberspark uobjcoll build -v --platform=pc --arch=x86_32 --cpu=generic .
	@echo built uxmhf collection successfully!

.PHONY: stage
stage:
	@echo creating staging
	uberspark staging create uxmhf-pc 
	uberspark staging config-set --setting-name=uobj_binary_image_size --setting-value=0x14A00000
	# uberspark staging config-set --root-dir=/home/yeeb16 --setting-name=bridge_cc_bridge --setting-value=container/amd64/x86_32/generic/gcc/v5.5.0
	# uberspark staging config-set --root-dir=/home/yeeb16 --setting-name=bridge_cc_bridge --setting-value=container/amd64/x86_32/generic/compcert/uxmhf-test
	uberspark staging config-set --setting-name=bridge_cc_bridge --setting-value=container/amd64/x86_32/generic/compcert/v3.1

#uxmhf-test
#v5.4.0
	uberspark staging config-set --setting-name=bridge_as_bridge --setting-value=container/amd64/x86_32/generic/gnu-as/v2.26.1
	uberspark staging config-set --setting-name=bridge_ld_bridge --setting-value=container/amd64/x86_32/generic/gnu-ld/v2.26.1
	@echo staging created successfully!

.PHONY: clean
clean: 
	rm -rf _build
