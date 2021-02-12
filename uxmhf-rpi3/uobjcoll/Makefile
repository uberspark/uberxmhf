#   xmhf-rpi3 Makefile refactored to use überSpark
#
#   micro-hypervisor for raspberry pi 3
#   
#   author: amit vasudevan <amitvasudevan@acm.org>, matt mccormack <matthew.mccormack@live.com>
#

COMPILER := uberspark/bridges/container/amd64/cc-bridge/armv8_32/generic/gcc/v4.9.3
ASSEMBLER := uberspark/bridges/container/amd64/as-bridge/armv8_32/generic/gnu-as/v2.26.1
LINKER := uberspark/bridges/container/amd64/ld-bridge/armv8_32/generic/gnu-ld/v2.26.1

SPARK_NAMESPACE := $(shell uberspark staging list | grep rpi3)
SPARK_CC := $(shell uberspark staging --setting-name=cc_bridge_namespace config-get)
SPARK_AS := $(shell uberspark staging --setting-name=as_bridge_namespace config-get)
SPARK_LD := $(shell uberspark staging --setting-name=ld_bridge_namespace config-get)

###### targets

.PHONY: all
all: prep build

.PHONY: build
build: 
	@echo building xmhf-rpi3...
	uberspark staging switch rpi3 
	uberspark -v
	@echo built xmhf-rpi3 successfully!


.PHONY: prep
prep:
ifeq ("$(SPARK_NAMESPACE)", "")
	uberspark staging create rpi3
endif
#ifneq ("$(SPARK_CC)", "$(COMPILER)")
	uberspark staging config-set --setting-name=cc_bridge_namespace --setting-value=$(COMPILER)
#endif
#ifneq ("$(SPARK_AS)", "$(ASSEMBLER)")
	uberspark staging config-set --setting-name=as_bridge_namespace --setting-value=$(ASSEMBLER)
#endif
#ifneq ("$(SPARK_LD)", "$(LINKER)")
	uberspark staging config-set --setting-name=ld_bridge_namespace --setting-value=$(LINKER)
#endif
	uberspark staging config-set --setting-name=binary_page_size --setting-value=0x1000
	uberspark staging config-set --setting-name=binary_uobj_section_alignment --setting-value=0x1000
	uberspark staging config-set --setting-name=binary_uobj_default_section_size --setting-value=0x1000
	uberspark staging config-set --setting-name=uobj_binary_image_alignment --setting-value=0x1000
	uberspark staging config-set --setting-name=uobjcoll_binary_image_load_address --setting-value=0x00007000
	uberspark staging config-set --setting-name=uobj_binary_image_size --setting-value=0x00200000
	#uberspark staging config-set --setting-name=uobjcoll_binary_image_section_alignment --setting-value=0x1000



.PHONY: clean
clean: 
	rm -rf _triage
