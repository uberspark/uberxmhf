AC_INIT([xmhf], [1.0.0])
#AC_CONFIG_AUX_DIR([build-aux]) # use this if\when switching to automake

#AC_PROG_INSTALL

#AC_PROG_CC
# disabled for now. this macro would test gcc with compiling a
# 'normal' program, which fails with the 'tools' gcc because
# it doesn't have its -lgcc etc.

# simple configuration of tools. (just looks for matching binary
# on PATH)
AC_CHECK_PROG([CC], [gcc], [gcc])
AC_CHECK_PROG([CCERT], [ccomp], [ccomp])
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

# find path to -lgcc
AC_SUBST([CCLIB], [`$CC -m32 --print-file-name=`])

# user-defined options

# target cpu
AC_SUBST([TARGET_CPU])
AC_ARG_WITH([target_cpu],
        AS_HELP_STRING([--with-target-cpu=@<:@CPU@:>@],
                [select target cpu (x86)]),
                , [with_target_cpu=x86])
TARGET_CPU=$[]with_target_cpu

# target container
AC_SUBST([TARGET_CONTAINER])
AC_ARG_WITH([target_container],
        AS_HELP_STRING([--with-target-container=@<:@CONTAINER@:>@],
                [select target container (vmx)]),
                , [with_target_container=vmx])
TARGET_CONTAINER=$[]with_target_container

# target platform
AC_SUBST([TARGET_PLATFORM])
AC_ARG_WITH([target_platform],
        AS_HELP_STRING([--with-target-platform=@<:@PLATFORM@:>@],
                [select target platform (x86pc)]),
                , [with_target_platform=x86pc])
TARGET_PLATFORM=$[]with_target_platform


# XMHF hypapps to be built
AC_SUBST([XMHF_HYPAPPS])
AC_ARG_WITH([xmhf_hypapps],
        AS_HELP_STRING([--with-xmhf-hypapps=@<:@path@:>@],
                [space delimited paths to hypapp source root directories]),
                , [with_xmhf_hypapps=])
XMHF_HYPAPPS=$[]with_xmhf_hypapps

#debugging
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


# XMHF libs source directory
AC_SUBST([XMHFLIBS_SRC])
AC_ARG_WITH([libbaremetalsrc],
        AS_HELP_STRING([--with-libbaremetalsrc=@<:@path@:>@],
                [path to libbaremetal source directory]),
                , [with_libbaremetalsrc=./xmhf-libs])
XMHFLIBS_SRC=$[]with_libbaremetalsrc
AC_CHECK_FILE([${XMHFLIBS_SRC}/libxmhfc],
        ,
        AC_MSG_FAILURE([libs not found at "${XMHFLIBS_SRC}"]))


AC_SUBST([prefix])
AC_SUBST([exec_prefix])
AC_SUBST([datadir])
AC_SUBST([libdir])
AC_SUBST([includedir])
AC_SUBST([pkgdatadir], ['${datadir}/AC_PACKAGE_NAME'])
AC_SUBST([pkgconfigdir], ['${libdir}/pkgconfig'])
AC_SUBST([pkgincludedir], ['${includedir}/AC_PACKAGE_NAME'])

AC_CONFIG_FILES(
			[common.mk]
			[Makefile]
			[SLABS])

AC_OUTPUT
