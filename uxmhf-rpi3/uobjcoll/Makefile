#   xmhf-rpi3 Makefile refactored to use überSpark
#
#   micro-hypervisor for raspberry pi 3
#   
#   author: amit vasudevan <amitvasudevan@acm.org>, matt mccormack <matthew.mccormack@live.com>
#

###### targets

.PHONY: all
all: 
	@echo building xmhf-rpi3...
	uberspark staging switch rpi3 
	uberspark uobjcoll build -v --platform=rpi3 --arch=armv8_32 --cpu=generic .
	@echo built xmhf-rpi3 successfully!


.PHONY: clean
clean: 
	rm -rf _build
