AC_INIT([xmhf], [6.1.0])
AC_CONFIG_AUX_DIR([build-aux]) # use this if\when switching to automake

AC_PROG_INSTALL

#AC_PROG_CC
# disabled for now. this macro would test gcc with compiling a
# 'normal' program, which fails with the 'tools' gcc because
# it doesn't have its -lgcc etc.

# simple configuration of tools. (just looks for matching binary
# on PATH)
AC_CHECK_PROG([CC], [gcc], [gcc])
AC_CHECK_PROG([AS], [as], [as])
AC_CHECK_PROG([LD], [ld], [ld])
AC_CHECK_PROG([OBJDUMP], [objdump], [objdump])
AC_CHECK_PROG([OBJCOPY], [objcopy], [objcopy])
AC_CHECK_PROG([STRIP], [strip], [strip])
AC_CHECK_PROG([RM], [rm -f], [rm -f])
AC_CHECK_PROG([CP], [cp], [cp])
AC_CHECK_PROG([TAR], [tar], [tar])
AC_CHECK_PROG([SED], [sed], [sed])
AC_CHECK_PROG([MKDIR], [mkdir], [mkdir])
AC_CHECK_PROG([CAT], [cat], [cat])

# user-defined options

# 64-bit?
AC_SUBST([TARGET_SUBARCH])
AC_ARG_WITH([target_subarch],
        AS_HELP_STRING([--with-target-subarch=@<:@SUBARCH@:>@],
                [select target hardware platform (i386, amd64)]),
                , [with_target_subarch=i386])
TARGET_SUBARCH=$[]with_target_subarch

# When 64-bit, set maximum physical address (default 0x400000000 is 16 GiB)
AC_SUBST([AMD64_MAX_PHYS_ADDR])
AC_ARG_WITH([amd64_max_phys_addr],
        AS_HELP_STRING([--with-amd64-max-phys-addr=@<:@MAX_PHYS_ADDR@:>@],
                [select max physical address when using subarch amd64]),
                , [with_amd64_max_phys_addr=0x400000000])
AMD64_MAX_PHYS_ADDR=$[]with_amd64_max_phys_addr

# find path to -lgcc
AC_SUBST([CCLIB])
AS_IF([test "x${with_target_subarch}" != "xamd64"],
      [CCLIB=`$CC -m32 --print-file-name=`],
      [CCLIB=`$CC -m64 --print-file-name=`])

# find path to -lgcc in x86 (for bootloader)
# TODO: this is a workaround. Should cross-compile everything in bootloader
# (i.e. use i686-linux-gnu-gcc, i686-linux-gnu-ld, etc.)
AC_CHECK_PROG([CC32], [i686-linux-gnu-gcc], [i686-linux-gnu-gcc], [gcc])
AC_SUBST([BCCLIB], [`$CC32 -m32 --print-file-name=`])

# target platform
AC_SUBST([TARGET_PLATFORM])
AC_ARG_WITH([target_platform],
        AS_HELP_STRING([--with-target-platform=@<:@PLATFORM@:>@],
                [select target platform (x86-pc)]),
                , [with_target_platform=x86-pc])
TARGET_PLATFORM=$[]with_target_platform

# target architecture
AC_SUBST([TARGET_ARCH])
AC_ARG_WITH([target_arch],
        AS_HELP_STRING([--with-target-arch=@<:@ARCH@:>@],
                [select target architecture (x86-vmx, x86-svm)]),
                , [with_target_arch=x86-vmx])
TARGET_ARCH=$[]with_target_arch

# Allow hypapps to disable integrated GPU's IOMMU when needed due to hardware quirks.
# WARNING: If set this config, then XMHF must trust ALL code that can disable igfx's IOMMU and configuring igfx
# Default: no
AC_SUBST([ALLOW_HYPAPP_DISABLE_IGFX_IOMMU])
AC_ARG_ENABLE([allow_hypapp_disable_igfx_iommu],
        AS_HELP_STRING([--allow-hypapp-disable-igfx-iommu@<:@=yes|no@:>@],
                [Allow a hypapp to disable igfx's IOMMU when needed due to igfx's hardware quirks. WARNING: If set this config, then XMHF MUST TRUST ALL code that can disable igfx's IOMMU and configuring igfx]),
                , [allow_hypapp_disable_igfx_iommu=no])
AS_IF([test "x${allow_hypapp_disable_igfx_iommu}" != "xno"],
      [ALLOW_HYPAPP_DISABLE_IGFX_IOMMU=y],
      [ALLOW_HYPAPP_DISABLE_IGFX_IOMMU=n])

# Enable CPU quiescing in guest memory/PIO access traps
# Default: yes
AC_SUBST([ENABLE_QUIESCING_IN_GUEST_MEM_PIO_TRAPS])
AC_ARG_ENABLE([quiesce_in_guest_mem_pio_traps],
        AS_HELP_STRING([--enable-quiesce-in-guest-mem-pio-traps@<:@=yes|no@:>@],
                [enable CPU quiescing in guest memory/PIO access traps]),
                , [enable_quiesce_in_guest_mem_pio_traps=yes])
AS_IF([test "x${enable_quiesce_in_guest_mem_pio_traps}" != "xno"],
      [ENABLE_QUIESCING_IN_GUEST_MEM_PIO_TRAPS=y],
      [ENABLE_QUIESCING_IN_GUEST_MEM_PIO_TRAPS=n])

# Enable --gc-sections in ld to remove unused symbols, reduce secureloader size
# Default: yes
AC_SUBST([ENABLE_LD_GC_SECTIONS])
AC_ARG_ENABLE([ld_gc_sections],
        AS_HELP_STRING([--enable-ld-gc-sections@<:@=yes|no@:>@],
                [enable garbage collecting unused symbols in ld]),
                , [ld_gc_sections=yes])
AS_IF([test "x${ld_gc_sections}" != "xno"],
      [ENABLE_LD_GC_SECTIONS=y],
      [ENABLE_LD_GC_SECTIONS=n])

# debug symbols (-g in gcc)
AC_SUBST([DEBUG_SYMBOLS])
AC_ARG_ENABLE([debug_symbols],
        AS_HELP_STRING([--enable-debug-symbols@<:@=yes|no@:>@],
                [enable debug symbols]),
                , [enable_debug_symbols=no])
AS_IF([test "x${enable_debug_symbols}" != "xno"],
      [DEBUG_SYMBOLS=y],
      [DEBUG_SYMBOLS=n])

# Workaround to run in QEMU
AC_SUBST([DEBUG_QEMU])
AC_ARG_ENABLE([debug_qemu],
        AS_HELP_STRING([--enable-debug-qemu@<:@=yes|no@:>@],
                [enable QEMU workaround for debugging]),
                , [enable_debug_qemu=no])
AS_IF([test "x${enable_debug_qemu}" != "xno"],
      [DEBUG_QEMU=y],
      [DEBUG_QEMU=n])

AC_SUBST([HIDE_X2APIC])
AC_ARG_ENABLE([hide_x2apic],
        AS_HELP_STRING([--enable-hide-x2apic@<:@=yes|no@:>@],
                [remove x2APIC from CPUID (workaround bug in x2APIC EOI)]),
                , [enable_hide_x2apic=no])
AS_IF([test "x${enable_hide_x2apic}" != "xno"],
      [HIDE_X2APIC=y],
      [HIDE_X2APIC=n])

# Optimization when running in nested virtualization
AC_SUBST([OPTIMIZE_NESTED_VIRT])
AC_ARG_ENABLE([optimize_nested_virt],
        AS_HELP_STRING([--enable-optimize-nested-virt@<:@=yes|no@:>@],
                [enable optimization for running in nested virtualization]),
                , [enable_optimize_nested_virt=no])
AS_IF([test "x${enable_optimize_nested_virt}" != "xno"],
      [OPTIMIZE_NESTED_VIRT=y],
      [OPTIMIZE_NESTED_VIRT=n])

# Support for updating Intel microcode (a.k.a. ucode)
AC_SUBST([UPDATE_INTEL_UCODE])
AC_ARG_ENABLE([update_intel_ucode],
        AS_HELP_STRING([--enable-update-intel-ucode@<:@=yes|no@:>@],
                [enable support for updating Intel microcode]),
                , [enable_update_intel_ucode=no])
AS_IF([test "x${enable_update_intel_ucode}" != "xno"],
      [UPDATE_INTEL_UCODE=y],
      [UPDATE_INTEL_UCODE=n])

AC_SUBST([SKIP_RUNTIME_BSS])
AC_ARG_ENABLE([skip_runtime_bss],
        AS_HELP_STRING([--enable-skip-runtime-bss@<:@=yes|no@:>@],
                [do not include runtime's BSS to save time, only when no DRT]),
                , [enable_skip_runtime_bss=no])
AS_IF([test "x${enable_skip_runtime_bss}" != "xno"],
      [SKIP_RUNTIME_BSS=y],
      [SKIP_RUNTIME_BSS=n])

AC_SUBST([SKIP_INIT_SMP])
AC_ARG_ENABLE([skip_init_smp],
        AS_HELP_STRING([--enable-skip-init-smp@<:@=yes|no@:>@],
                [do not start APs in bootloader, only when no DRT]),
                , [enable_skip_init_smp=no])
AS_IF([test "x${enable_skip_init_smp}" != "xno"],
      [SKIP_INIT_SMP=y],
      [SKIP_INIT_SMP=n])

AC_SUBST([SKIP_BOOTLOADER_HASH])
AC_ARG_ENABLE([skip_bootloader_hash],
        AS_HELP_STRING([--enable-skip-bootloader-hash@<:@=yes|no@:>@],
                [skip computing hash in bootloader, only when no DRT]),
                , [enable_skip_bootloader_hash=no])
AS_IF([test "x${enable_skip_bootloader_hash}" != "xno"],
      [SKIP_BOOTLOADER_HASH=y],
      [SKIP_BOOTLOADER_HASH=n])

# Support for nested virtualization
AC_SUBST([NESTED_VIRTUALIZATION])
AC_ARG_ENABLE([nested_virtualization],
        AS_HELP_STRING([--enable-nested-virtualization@<:@=yes|no@:>@],
                [enable support for updating Intel microcode]),
                , [enable_nested_virtualization=no])
AS_IF([test "x${enable_nested_virtualization}" != "xno"],
      [NESTED_VIRTUALIZATION=y],
      [NESTED_VIRTUALIZATION=n])

# When supporting nested virtualization, maximum number of EPTs per CPU
# When NESTED_VIRTUALIZATION=n, this configuration is ignored
AC_SUBST([VMX_NESTED_MAX_ACTIVE_EPT])
AC_ARG_WITH([vmx_nested_max_active_ept],
        AS_HELP_STRING([--with-vmx-nested-max-active-ept=@<:@VMX_NESTED_MAX_ACTIVE_EPT@:>@],
                [when nested virtualization, number of active EPTs per CPU]),
                , [with_vmx_nested_max_active_ept=8])
VMX_NESTED_MAX_ACTIVE_EPT=$[]with_vmx_nested_max_active_ept

# When supporting nested virtualization, maximum number of EPTs per CPU
# When NESTED_VIRTUALIZATION=n, this configuration is ignored
AC_SUBST([VMX_NESTED_EPT02_PAGE_POOL_SIZE])
AC_ARG_WITH([vmx_nested_ept02_page_pool_size],
        AS_HELP_STRING([--with-vmx-nested-ept02-page-pool-size=@<:@VMX_NESTED_EPT02_PAGE_POOL_SIZE@:>@],
                [when nested virtualization, size of each EPT02 page pool]),
                , [with_vmx_nested_ept02_page_pool_size=512])
VMX_NESTED_EPT02_PAGE_POOL_SIZE=$[]with_vmx_nested_ept02_page_pool_size

# When supporting nested virtualization, whether allow MSR bitmap
# When NESTED_VIRTUALIZATION=n, this configuration is ignored
AC_SUBST([VMX_NESTED_MSR_BITMAP])
AC_ARG_ENABLE([vmx_nested_msr_bitmap],
        AS_HELP_STRING([--enable-vmx-nested-msr-bitmap@<:@=yes|no@:>@],
                [when nested virtualization, enable support for MSR bitmap]),
                , [enable_vmx_nested_msr_bitmap=yes])
AS_IF([test "x${enable_vmx_nested_msr_bitmap}" != "xno"],
      [VMX_NESTED_MSR_BITMAP=y],
      [VMX_NESTED_MSR_BITMAP=n])

AC_SUBST([DEBUG_SERIAL])
AC_SUBST([DEBUG_SERIAL_PORT])
AC_ARG_ENABLE([debug_serial],
        AS_HELP_STRING([--enable-debug-serial@<:@=PORT|no@:>@],
                [enable serial debugging on specified port]),
                , [enable_debug_serial=0x3f8])
AS_IF([test "x${enable_debug_serial}" != "xno"],
      [DEBUG_SERIAL=y
       DEBUG_SERIAL_PORT=$[]enable_debug_serial],
      [DEBUG_SERIAL=n])

AC_SUBST([DEBUG_VGA])
AC_ARG_ENABLE([debug_vga],
        AS_HELP_STRING([--enable-debug-vga@<:@=yes|no@:>@],
                [enable vga debugging]),
                , [enable_debug_vga=no])
AS_IF([test "x${enable_debug_vga}" != "xno"],
      [DEBUG_VGA=y],
      [DEBUG_VGA=n])

AC_SUBST([DEBUG_EVENT_LOGGER])
AC_ARG_ENABLE([debug_event_logger],
        AS_HELP_STRING([--enable-debug-event-logger@<:@=yes|no@:>@],
                [enable event logger debugging]),
                , [enable_debug_event_logger=no])
AS_IF([test "x${enable_debug_event_logger}" != "xno"],
      [DEBUG_EVENT_LOGGER=y],
      [DEBUG_EVENT_LOGGER=n])

AC_SUBST([MP_VERSION])
AC_ARG_ENABLE([mp],
        AS_HELP_STRING([--enable-mp@<:@=yes|no@:>@],
                [enable multiprocessor]),
                , [enable_mp=yes])
AS_IF([test "x${enable_mp}" != "xno"],
      [MP_VERSION=y],
      [MP_VERSION=n])


# selectively enable/disable Dynamic Root-of-Trust (DRT)
AC_SUBST([DRT])
AC_ARG_ENABLE([drt],
        AS_HELP_STRING([--enable-drt@<:@=yes|no@:>@],
                [enable Dynamic Root-of-Trust (DRT)]),
                , [enable_drt=yes])
AS_IF([test "x${enable_drt}" != "xno"],
      [DRT=y],
      [DRT=n])

# selectively enable/disable DMA protection (DMAP)
AC_SUBST([DMAP])
AC_ARG_ENABLE([dmap],
        AS_HELP_STRING([--enable-dmap@<:@=yes|no@:>@],
                [enable DMA protection]),
                , [enable_dmap=yes])
AS_IF([test "x${enable_dmap}" != "xno"],
      [DMAP=y],
      [DMAP=n])

# select address of SL and runtime
AC_SUBST([SL_BASE])
AC_ARG_WITH([sl_base],
        AS_HELP_STRING([--with-sl-base=@<:@SL_BASE@:>@],
                [select base address of SL and runtime (e.g. 0x10000000)]),
                , [with_sl_base=0x10000000])
SL_BASE=$[]with_sl_base

# select optimization level
AC_SUBST([OPT_FLAGS])
AC_ARG_WITH([opt],
        AS_HELP_STRING([--with-opt=@<:@OPT@:>@],
                [select optimization level (-O1, -O3, ...)]),
                , [with_opt=])
OPT_FLAGS=$[]with_opt

# libbaremetal source directory
AC_SUBST([LIBBAREMETAL_SRC])
AC_ARG_WITH([libbaremetalsrc],
        AS_HELP_STRING([--with-libbaremetalsrc=@<:@path@:>@],
                [path to libbaremetal source directory]),
                , [with_libbaremetalsrc=./xmhf/src/libbaremetal])
LIBBAREMETAL_SRC=$[]with_libbaremetalsrc
# make absolute
dnl AS_IF([test "x${LIBBAREMETAL_SRC:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$LIBBAREMETAL_SRC])

AC_CHECK_FILE([${LIBBAREMETAL_SRC}/libxmhfc],
        ,
        AC_MSG_FAILURE([libbaremetal not found at "${LIBBAREMETAL_SRC}"]))

# libtommath source directory
AC_SUBST([LIBTOMMATH_SRC])
AC_ARG_WITH([libtommathsrc],
        AS_HELP_STRING([--with-libtommathsrc=@<:@path@:>@],
                [path to libtommath source directory]),
                , [with_libtommathsrc=./xmhf/third-party/libtommath])
LIBTOMMATH_SRC=$[]with_libtommathsrc
AC_CHECK_FILE([${LIBTOMMATH_SRC}/tommath.h],
        ,
        AC_MSG_FAILURE([libtommath not found at "${LIBTOMMATH_SRC}"]))

# libtomcrypt source directory
AC_SUBST([LIBTOMCRYPT_SRC])
AC_ARG_WITH([libtomcryptsrc],
        AS_HELP_STRING([--with-libtomcryptsrc=@<:@path@:>@],
                [path to libtomcrypt source directory]),
                , [with_libtomcryptsrc=./xmhf/third-party/libtomcrypt])
LIBTOMCRYPT_SRC=$[]with_libtomcryptsrc
AC_CHECK_FILE([${LIBTOMCRYPT_SRC}/src/headers/tomcrypt.h],
        ,
        AC_MSG_FAILURE([libtomcrypt not found at "${LIBTOMCRYPT_SRC}"]))

# EMHF app root directory
AC_SUBST([APP_ROOT])
AC_ARG_WITH([approot],
        AS_HELP_STRING([--with-approot=@<:@path@:>@],
                [path to EMHF app source directory]),
                , [with_approot=./hypapps/app])
APP_ROOT=$[]with_approot
# AC_CONFIG_SUBDIRS fails silently on absolute paths
AS_IF([test "x${APP_ROOT:0:1}" == "x/"],
            AC_MSG_FAILURE([approot must be a relative path.]))
# make absolute
dnl AS_IF([test "x${APP_ROOT:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$APP_ROOT])

# Choose offset of TrustVisor hypercall number for L2 in nested virtualization
# When NESTED_VIRTUALIZATION=n, this configuration is ignored
AC_SUBST([TRUSTVISOR_L2_OFFSET])
AC_ARG_WITH([trustvisor_l2_offset],
        AS_HELP_STRING([--with-trustvisor-l2-offset=@<:@TRUSTVISOR_L2_OFFSET@:>@],
                [offset of TrustVisor hypercall number for L2]),
                , [with_trustvisor_l2_offset=0x4c415000U])
TRUSTVISOR_L2_OFFSET=$[]with_trustvisor_l2_offset

AC_SUBST([EMHFCOREDIR])
AC_ARG_WITH([emhfcore],
        AS_HELP_STRING([--with-emhfcore=@<:@path@:>@],
                [path to NO emhfcore XXX FIXME app]),
                , [with_emhfcore=./emhfcore/x86])


# todo- maybe test here if configured path actually has emhfcore in it
EMHFCOREDIR=$[]with_emhfcore
# make absolute
dnl AS_IF([test "x${EMHFCOREDIR:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$EMHFCOREDIR])

AC_SUBST([CMOCKDIR])
AC_ARG_WITH([cmock],
        AS_HELP_STRING([--with-cmock=@<:@path@:>@],
                [path to cmock]),
                , [with_cmock=./tools/cmock])
CMOCKDIR=$[]with_cmock

AC_SUBST([UNITYDIR])
AC_ARG_WITH([unity],
        AS_HELP_STRING([--with-unity=@<:@path@:>@],
                [path to unity]),
                , [with_unity=./tools/cmock/vendor/unity])
UNITYDIR=$[]with_unity

AC_SUBST([prefix])
AC_SUBST([exec_prefix])
AC_SUBST([datadir])
AC_SUBST([libdir])
AC_SUBST([includedir])
AC_SUBST([pkgdatadir], ['${datadir}/AC_PACKAGE_NAME'])
AC_SUBST([pkgconfigdir], ['${libdir}/pkgconfig'])
AC_SUBST([pkgincludedir], ['${includedir}/AC_PACKAGE_NAME'])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
