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
# xmhf/src/xmhf-core/initbs/arch/x86/common/xc-xcphandler-x86.c:(.text+0x14e): undefined reference to `xmhf_xcphandler_arch_hub'
# xc-xcphandler-x86.o:xmhf/src/xmhf-core/initbs/arch/x86/common/xc-xcphandler-x86.c:(.text+0x16e): more undefined references to `xmhf_xcphandler_arch_hub' follow
# xc-baseplatform-x86vmx.o: In function `xmhf_baseplatform_arch_x86_smpinitialize_commonstart':
# xmhf/src/xmhf-core/initbs/arch/x86/vmx/xc-baseplatform-x86vmx.c:(.text+0x70a): undefined reference to `init_entry'
# make[1]: *** [xmhf-core] Error 1

C_SOURCES += $(wildcard $(srcdir)/init/*.c)
C_SOURCES += $(shell find $(srcdir)/init/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/init/arch/x86/vmx/ -type f -name '*.c')

#-----------------------------------------------------------------------
#init-entry.o: In function `init_entry':
#/xmhf/src/xmhf-core/init/init-entry.c:(.text+0xa1): undefined reference to `xc_api_partition_create'
#/xmhf/src/xmhf-core/init/init-entry.c:(.text+0x1fb): undefined reference to `xc_hypapp_initialization'
#/xmhf/src/xmhf-core/init/init-entry.c:(.text+0x293): undefined reference to `xc_api_partition_startcpu'
#xc-init-richguest.o: In function `xmhf_richguest_setup':
#xmhf/src/xmhf-core/init/xc-init-richguest.c:(.text+0x3c): undefined reference to `xc_api_partition_addcpu'
#xc-init-richguest-x86vmx.o: In function `_vmx_setupEPT':
#xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x297f): undefined reference to `xc_api_hpt_setentry'
#xc-init-richguest-x86vmx.o: In function `xmhf_richguest_arch_setupguestOSstate':
#xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2b44): undefined reference to `xc_api_cpustate_get'
#xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2be8): undefined reference to `xc_api_cpustate_set'
#xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2c80): undefined reference to `xc_api_cpustate_set'
#xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2d39): undefined reference to `xc_api_cpustate_set'
#xmhf/src/xmhf-core/init/arch/x86/vmx/xc-init-richguest-x86vmx.c:(.text+0x2e9d): undefined reference to `xc_api_cpustate_set'
#make[1]: *** [xmhf-core] Error 1


C_SOURCES += $(wildcard $(srcdir)/ihub/*.c)
C_SOURCES += $(shell find $(srcdir)/ihub/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/ihub/arch/x86/vmx/ -type f -name '*.c')

##------------------------------------------------------------------------
## xc-ihub-apihub.o: In function `xmhf_apihub_fromhypapp':
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x185): undefined reference to `xc_api_hpt_setprot'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x1b2): undefined reference to `xc_api_hpt_getprot'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x20b): undefined reference to `xc_api_hpt_setentry'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x238): undefined reference to `xc_api_hpt_getentry'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x26b): undefined reference to `xc_api_hpt_flushcaches'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x292): undefined reference to `xc_api_hpt_flushcaches_smp'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x2bf): undefined reference to `xc_api_hpt_lvl2pagewalk'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x350): undefined reference to `xc_api_trapmask_set'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x3d5): undefined reference to `xc_api_trapmask_clear'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x45a): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x4a1): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/xc-ihub-apihub.c:(.text+0x4df): undefined reference to `xc_api_platform_shutdown'
## xc-ihub-xcphandler-x86.o: In function `xmhf_xcphandler_arch_hub':
# xmhf/src/xmhf-core/ihub/arch/x86/common/xc-ihub-xcphandler-x86.c:(.text+0x2d): undefined reference to `xmhf_smpguest_arch_eventhandler_nmiexception'
## xc-ihub-x86vmx.o: In function `xmhf_partition_eventhub_arch_x86vmx':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x8e): undefined reference to `xc_api_partition_getcontextdesc'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x158): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x266): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x32b): undefined reference to `xc_api_cpustate_get'
## xc-ihub-x86vmx.o: In function `_vmx_intercept_handler':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x434): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x6bd): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x76f): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x821): undefined reference to `xc_api_cpustate_get'
## xc-ihub-x86vmx.o: xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0xa8a): more undefined references to `xc_api_cpustate_get' follow
## xc-ihub-x86vmx.o: In function `_vmx_intercept_handler':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0xb72): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0xc9a): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0xd98): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0xfd9): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x10dc): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x11b2): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x129a): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x14ee): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x15f1): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1799): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x189c): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1950): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1a53): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1bac): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1caf): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1edf): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x1fe2): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2051): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x20fb): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2226): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x229e): undefined reference to `xc_api_cpustate_set'
## xc-ihub-x86vmx.o: In function `_vmx_propagate_cpustate_guestx86gprs':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2385): undefined reference to `xc_api_cpustate_set'
## xc-ihub-x86vmx.o: In function `vmx_handle_intercept_cr0access_ug':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x27e0): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2874): undefined reference to `xc_api_cpustate_set'
## xc-ihub-x86vmx.o: In function `_vmx_handle_intercept_rdmsr':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x29b0): undefined reference to `xc_api_cpustate_get'
## xc-ihub-x86vmx.o: In function `_vmx_handle_intercept_wrmsr':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2b3d): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2c23): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2c8c): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-x86vmx.c:(.text+0x2cf5): undefined reference to `xc_api_cpustate_set'
## xc-ihub-richguest-x86vmx.o: In function `xmhf_smpguest_arch_x86vmx_handle_guestmemoryreporting':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x5d): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x10f): undefined reference to `xc_api_cpustate_get'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x53f): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x6a0): undefined reference to `xc_api_cpustate_set'
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x72f): undefined reference to `xc_api_cpustate_set'
## xc-ihub-richguest-x86vmx.o: In function `xmhf_smpguest_arch_memcpyto':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x7ac): undefined reference to `xc_api_hpt_lvl2pagewalk'
## xc-ihub-richguest-x86vmx.o: In function `xmhf_smpguest_arch_readu16':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x866): undefined reference to `xc_api_hpt_lvl2pagewalk'
## xc-ihub-richguest-x86vmx.o: In function `xmhf_smpguest_arch_writeu16':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0x8fc): undefined reference to `xc_api_hpt_lvl2pagewalk'
## xc-ihub-richguest-x86vmx.o: In function `xmhf_smpguest_arch_memcpyfrom':
# xmhf/src/xmhf-core/ihub/arch/x86/vmx/xc-ihub-richguest-x86vmx.c:(.text+0xa8c): undefined reference to `xc_api_hpt_lvl2pagewalk'


C_SOURCES += $(wildcard $(srcdir)/coreapi/*.c)
C_SOURCES += $(shell find $(srcdir)/coreapi/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/coreapi/arch/x86/vmx/ -type f -name '*.c')

#------------------------------------------------------------------------------------------
#xc-coreapi-x86vmx.o: In function `_xc_api_partition_arch_addcpu_setupbasestate':
#xmhf/src/xmhf-core/coreapi/arch/x86/vmx/xc-coreapi-x86vmx.c:(.text+0x232f): undefined reference to `xmhf_parteventhub_arch_x86vmx_entry'



C_SOURCES += $(wildcard $(srcdir)/shared/*.c)
C_SOURCES += $(shell find $(srcdir)/shared/arch/x86/common/ -type f -name '*.c')
C_SOURCES += $(shell find $(srcdir)/shared/arch/x86/vmx/ -type f -name '*.c')

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

# LLC flags
LLC_ATTR = -3dnow,-3dnowa,-64bit,-64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop


# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): testslab initbs $(OBJECTS) 
	cd $(XMHF_CORE_OBJECTS_DIR) && cp -f $(srcdir)/xc.lscript xc.lscript.c
	cd $(XMHF_CORE_OBJECTS_DIR) && $(CC) $(CFLAGS) -D__ASSEMBLY__ -P -E xc.lscript.c -o xc.lds
	cd $(XMHF_CORE_OBJECTS_DIR) && $(LD) --oformat elf32-i386 -T xc.lds -o $(THE_ARCHIVE).exe _objs_slab/xmhf-slab.slo $(OBJECTS_ARCHIVE) $(ADDL_LIBS) $(CCLIB)/lib/linux/libclang_rt.full-i386.a
	cd $(XMHF_CORE_OBJECTS_DIR) && $(OBJCOPY) --output-format=binary $(THE_ARCHIVE).exe $(THE_ARCHIVE).bin

.PHONY: testslab
testslab:
	mkdir -p $(XMHF_CORE_OBJECTS_DIR)
	cd $(XMHF_CORE_OBJECTS_DIR) && $(MAKE) -f $(srcdir)/slab-template/Makefile -w all

.PHONY: initbs
initbs:
	mkdir -p $(XMHF_CORE_OBJECTS_DIR)
	cd $(XMHF_CORE_OBJECTS_DIR) && $(MAKE) -f $(srcdir)/initbs/Makefile -w all

%.o: %.c   
	mkdir -p $(XMHF_CORE_OBJECTS_DIR)
	@echo Building "$(@F)" from "$<" 
	#$(CC) -c $(CFLAGS) -o $(XMHF_CORE_OBJECTS_DIR)/$(@F) $<
	$(CC) -S -emit-llvm $(CFLAGS) $< -o $(XMHF_CORE_OBJECTS_DIR)/$(@F).ll
	cd $(XMHF_CORE_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	cd $(XMHF_CORE_OBJECTS_DIR) && llc -O=0 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(XMHF_CORE_OBJECTS_DIR) && $(CC) -c $(CFLAGS) $(@F).s -o $(@F)

.PHONY: clean
clean:
	$(RM) -rf $(XMHF_CORE_OBJECTS_DIR)


