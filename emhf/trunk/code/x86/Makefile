# top-level makefile for emhf x86 platform 
# author: amit vasudevan (amitvasudevan@acm.org)

#-----build configuration
	#-----tools
	export CC = gcc
	export AS = as
	export LD = ld
	export OBJDUMP = objdump
	export OBJCOPY = objcopy
	export STRIP = strip
	export O_CC = /bin/gcc
	export RM = rm 
	export CP = cp
	export O_LD = /bin/ld
	export TAR = tar
	export SED = sed
	export MKDIR = mkdir
	export CAT = cat

	#-----basic flags for compiling and assembling
	CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
	CFLAGS += -fno-stack-protector
	CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
	CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
	CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare 
	CFLAGS += -Waggregate-return
	CFLAGS += -Winline
	CFLAGS += -m32 -march=k8 
	CFLAGS += -mno-mmx -mno-sse -mno-sse2 -mno-sse3 -mno-ssse3 
	CFLAGS += -mno-sse4.1 -mno-sse4.2 -mno-sse4 -mno-avx -mno-aes 
	CFLAGS += -mno-pclmul -mno-sse4a -mno-sse5 -mno-3dnow -mno-popcnt -mno-abm
	CFLAGS += -nostdinc -pipe -I$(EMHF_INCLUDEDIR) -I$(APP_INCLUDEDIR)

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

	#-----export CFLAGS and ASFLAGS
	ASFLAGS = $(CFLAGS) -D__ASSEMBLY__

	export CFLAGS
	export ASFLAGS


#-----build rules
.PHONY: all
all: common runtime app sl init hypervisor-$(TARGET_HWPLATFORM).bin.gz

common:
	#make libcommon first	
	cd libcommon && $(MAKE) -w all

runtime: common
	#make runtime
	cd runtime && $(MAKE) -w all

app: runtime common
	#make EMHFapp
	mkdir -p $(APPOBJECTSDIR)
	cd ../app && $(MAKE) -w all

sl: runtime common app
	#make sl
	# Double-dollar-sign required to cause make to provide literal dollar sign to perl
	# Objective: Create an escaped ASCII string containing the SHA-1 hash of the
	# runtime and pass it to the SL's makefile
	cd sl && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

init: sl runtime common app
	#make init	
	cd init && $(MAKE) -w all \
		RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLBELOW64K_INTEGRITY_HASH=\""$(shell ( dd if=./sl/sl.bin bs=1024 count=64 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\" \
		SLABOVE64K_INTEGRITY_HASH=\""$(shell ( dd if=./sl/sl.bin bs=1024 skip=64 count=1984 | sha1sum | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"

sl/sl.bin: sl
runtime/runtime.bin: runtime
hypervisor-$(TARGET_HWPLATFORM).bin.gz: sl/sl.bin runtime/runtime.bin
	# concatenate sl image and runtime image 
	$(CAT) ./sl/sl.bin ./runtime/runtime.bin > ./hypervisor.tmp.img
	gzip -c ./hypervisor.tmp.img > ./hypervisor-$(TARGET_HWPLATFORM).bin.gz
	$(RM) -rf ./hypervisor.tmp.img 

# cleanup rules
.PHONY: clean 
clean: 
	cd runtime && $(MAKE) -w clean
	cd sl && $(MAKE) -w clean
	cd init && $(MAKE) -w clean
	cd libcommon && $(MAKE) -w clean
	cd ../app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR)

