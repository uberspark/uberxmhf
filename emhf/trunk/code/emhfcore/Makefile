# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)

# experimental support
	export INIT_LATE := n
	export E820_UG_TEST := n
	export TEST_CPU_QUIESCE := n

# relatively stable support
# TODO: FIXME: Build breaks with some combinations of these options.
# They aren't really "options" anymore
# TODO: Control these with autoconf
	export DMAPROT := y
	export NESTED_PAGING := y


#-----build configuration
	#-----basic flags for compiling and assembling
	CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
	CFLAGS += -fno-stack-protector
	CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
	CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
	CFLAGS += -Wcast-qual -Wsign-compare
	CFLAGS += -Wno-bad-function-cast -Wall
	CFLAGS += -Waggregate-return
	CFLAGS += -Winline
	CFLAGS += -m32 -march=k8 
	CFLAGS += -mno-mmx -mno-sse -mno-sse2 -mno-sse3 -mno-ssse3 
	CFLAGS += -mno-sse4.1 -mno-sse4.2 -mno-sse4 -mno-avx -mno-aes 
	CFLAGS += -mno-pclmul -mno-sse4a -mno-sse5 -mno-3dnow -mno-popcnt -mno-abm
	CFLAGS += -nostdinc -pipe
	
	CFLAGS += $(ADDL_INCLUDES)

	#-----generate compiler/assembler defines from configuration options selected
	ifeq ($(NESTED_PAGING), y)
		CFLAGS += -D__NESTED_PAGING__
	endif
	ifeq ($(DEBUG_SERIAL), y)
		CFLAGS += -D__DEBUG_SERIAL__
		CFLAGS += -DDEBUG_PORT=$(DEBUG_SERIAL_PORT)
	endif
	ifeq ($(DEBUG_VGA), y)
		CFLAGS += -D__DEBUG_VGA__
	endif
	ifeq ($(MP_VERSION), y)
		CFLAGS += -D__MP_VERSION__
	endif

	CFLAGS += -D__DO_SENTER__

	ifeq ($(DMAPROT), y)
		CFLAGS += -D__DMAPROT__	
	endif
	ifeq ($(E820_UG_TEST), y)
		CFLAGS += -D__E820_UG_TEST__
	endif
	ifeq ($(TEST_CPU_QUIESCE), y)
		CFLAGS += -D__TEST_CPU_QUIESCE__
	endif

	# late initialization support (experimental)
	ifeq ($(INIT_LATE), y)
		CFLAGS += -D__INIT_LATE__ 
		CFLAGS += -DPERF_CRIT
	endif


	#-----export CFLAGS and ASFLAGS
	ASFLAGS = $(CFLAGS) -D__ASSEMBLY__

	export CFLAGS
	export ASFLAGS

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

	
