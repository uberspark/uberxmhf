#   xmhf-rpi3 Makefile refactored to use überSpark
#
#   micro-hypervisor for raspberry pi 3
#   
#   author: amit vasudevan <amitvasudevan@acm.org>, matt mccormack <matthew.mccormack@live.com>
#

###### targets

.PHONY: prep
prep:
	@echo configuring uberspark namespace
	uberspark staging create rpi3
	uberspark staging config-set --setting-name=bridge_cc_bridge --setting-value=container/amd64/armv8_32/generic/gcc/v4.9.3
	uberspark staging config-set --setting-name=bridge_as_bridge --setting-value=container/amd64/armv8_32/generic/gnu-as/v2.26.1
	uberspark staging config-set --setting-name=bridge_ld_bridge --setting-value=container/amd64/armv8_32/generic/gnu-ld/v2.26.1

.PHONY: all
all: 
	@echo building xmhf-rpi3...
	uberspark staging switch rpi3 
	uberspark uobjcoll build -v --platform=rpi3 --arch=armv8_32 --cpu=generic .
	@echo built xmhf-rpi3 successfully!


.PHONY: clean
clean: 
	rm -rf _build
