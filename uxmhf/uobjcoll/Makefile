#   uxmhf Makefile refactored to use the überSpark next-gen toolkit
#   
#   author: ethan joseph <ethanj217@gmail.com>
#			amit vasudevan <amitvasudevan@acm.org>
#

COMPILER := uberspark/bridges/container/amd64/cc-bridge/x86_32/generic/compcert/v3.1
ASSEMBLER := uberspark/bridges/container/amd64/as-bridge/x86_32/generic/gnu-as/v2.26.1
LINKER := uberspark/bridges/container/amd64/ld-bridge/x86_32/generic/gnu-ld/v2.26.1

SPARK_NAMESPACE := $(shell uberspark staging list | grep uxmhf-pc)
SPARK_CC := $(shell uberspark staging --setting-name=cc_bridge_namespace config-get)
SPARK_AS := $(shell uberspark staging --setting-name=as_bridge_namespace config-get)
SPARK_LD := $(shell uberspark staging --setting-name=ld_bridge_namespace config-get)

###### targets

.PHONY: all
all: prep build

.PHONY: build
build: 
	@echo building uxmhf collection...
	uberspark staging switch uxmhf-pc 
	uberspark build -v
	@echo built uxmhf collection successfully!

.PHONY: prep
prep:
ifeq ("$(SPARK_NAMESPACE)", "")
	uberspark staging create uxmhf-pc 
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
	uberspark staging config-set --setting-name=uobjcoll_image_load_address --setting-value=0x06200000
	uberspark staging config-set --setting-name=uobj_image_size --setting-value=0x14900000
	uberspark staging config-set --setting-name=page_size --setting-value=0x1000
	uberspark staging config-set --setting-name=uobj_section_alignment --setting-value=0x1000
	uberspark staging config-set --setting-name=uobj_default_section_size --setting-value=0x1000
	uberspark staging config-set --setting-name=uobj_image_alignment --setting-value=0x1000



.PHONY: clean
clean: 
	rm -rf _triage
