# makefile for XMHF core
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)

# grab list of all source files
C_SOURCES := $(wildcard $(srcdir)/*.c)

#C_SOURCES += $(wildcard $(srcdir)/initbs/*.c)
#C_SOURCES += $(shell find $(srcdir)/initbs/arch/x86/common/ -type f -name '*.c')
#C_SOURCES += $(shell find $(srcdir)/initbs/arch/x86/vmx/ -type f -name '*.c')

#----------------------------------------------------------------------
# xc-xcphandler-x86.o: In function `__xmhf_exception_handler_4':
# /mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/initbs/arch/x86/common/xc-xcphandler-x86.c:(.text+0x14e): undefined reference to `xmhf_xcphandler_arch_hub'
# xc-xcphandler-x86.o:/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/initbs/arch/x86/common/xc-xcphandler-x86.c:(.text+0x16e): more undefined references to `xmhf_xcphandler_arch_hub' follow
# xc-baseplatform-x86vmx.o: In function `xmhf_baseplatform_arch_x86_smpinitialize_commonstart':
# /mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/initbs/arch/x86/vmx/xc-baseplatform-x86vmx.c:(.text+0x70a): undefined reference to `init_entry'
# make[1]: *** [xmhf-core] Error 1

C_SOURCES += $(wildcard $(srcdir)/init/*.c)
C_SOURCES += $(shell find $(srcdir)/init/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/init/arch/x86/vmx/ -type f -name '*.c')

#-----------------------------------------------------------------------
#init-entry.o: In function `init_entry':
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/init-entry.c:(.text+0xa1): undefined reference to `xc_api_partition_create'
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/init-entry.c:(.text+0x1fb): undefined reference to `xc_hypapp_initialization'
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/init-entry.c:(.text+0x293): undefined reference to `xc_api_partition_startcpu'
#xc-init-richguest.o: In function `xmhf_richguest_setup':
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/xc-init-richguest.c:(.text+0x3c): undefined reference to `xc_api_partition_addcpu'
#xc-init-richguest-x86vmx.o: In function `_vmx_setupEPT':
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x297f): undefined reference to `xc_api_hpt_setentry'
#xc-init-richguest-x86vmx.o: In function `xmhf_richguest_arch_setupguestOSstate':
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2b44): undefined reference to `xc_api_cpustate_get'
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2be8): undefined reference to `xc_api_cpustate_set'
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2c80): undefined reference to `xc_api_cpustate_set'
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2d39): undefined reference to `xc_api_cpustate_set'
#/mnt/data/repos/xmhf-istcverification.git/xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2e9d): undefined reference to `xc_api_cpustate_set'
#make[1]: *** [xmhf-core] Error 1


#C_SOURCES += $(wildcard $(srcdir)/ihub/*.c)
#C_SOURCES += $(shell find $(srcdir)/ihub/arch/x86/common/ -type f -name '*.c')
#C_SOURCES += $(shell find $(srcdir)/ihub/arch/x86/vmx/ -type f -name '*.c')

#C_SOURCES += $(wildcard $(srcdir)/coreapi/*.c)
#C_SOURCES += $(shell find $(srcdir)/coreapi/arch/x86/common/ -type f -name '*.c')
#C_SOURCES += $(shell find $(srcdir)/coreapi/arch/x86/vmx/ -type f -name '*.c')


C_SOURCES += $(wildcard $(srcdir)/shared/*.c)

C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

# grab list of file names only for binary generation
C_SOURCES_FILENAMEONLY := $(notdir $(C_SOURCES))

OBJECTS_ARCHIVE := $(patsubst %.c, %.o, $(C_SOURCES_FILENAMEONLY))

# list of object dependencies
OBJECTS := $(patsubst %.c, %.o, $(C_SOURCES))

# folder where objects go
XMHF_CORE_OBJECTS_DIR = _objs_xmhf-core

# archive name
THE_ARCHIVE = xmhf-core

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS) 
	cd $(XMHF_CORE_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T $(srcdir)/xc.lds -o $(THE_ARCHIVE).exe $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	cd $(XMHF_CORE_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin

%.o: %.c   
	mkdir -p $(XMHF_CORE_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<" 
	$(CC) -c $(CFLAGS) -o $(XMHF_CORE_OBJECTS_DIR)/$(@F) $<

.PHONY: clean
clean:
	$(RM) -rf $(XMHF_CORE_OBJECTS_DIR)


