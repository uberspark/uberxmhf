AC_INIT([emhf], [0.2])
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

# find path to -lgcc
AC_SUBST([CCLIB], [`$CC -m32 --print-file-name=`])

# user-defined options

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

AC_SUBST([MP_VERSION])
AC_ARG_ENABLE([mp],
        AS_HELP_STRING([--enable-mp@<:@=yes|no@:>@],
                [enable multiprocessor]),
                , [enable_mp=yes])
AS_IF([test "x${enable_mp}" != "xno"],
      [MP_VERSION=y],
      [MP_VERSION=n])


# selectively disable DRTM/DMA protection
AC_SUBST([DRTM_DMA_PROTECTION])
AC_ARG_ENABLE([drtmdmaprotection],
        AS_HELP_STRING([--enable-drtmdmaprotection@<:@=yes|no@:>@],
                [enable DRTM and DMA protection]),
                , [enable_drtmdmaprotection=yes])
AS_IF([test "x${enable_drtmdmaprotection}" != "xno"],
      [DRTM_DMA_PROTECTION=y],
      [DRTM_DMA_PROTECTION=n])


# libbaremetal source directory
AC_SUBST([LIBBAREMETAL_SRC])
AC_ARG_WITH([libbaremetalsrc],
        AS_HELP_STRING([--with-libbaremetalsrc=@<:@path@:>@],
                [path to libbaremetal source directory]),
                , [with_libbaremetalsrc=../libbaremetal/src])
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
                , [with_libtommathsrc=../third-party/libtommath])
LIBTOMMATH_SRC=$[]with_libtommathsrc
AC_CHECK_FILE([${LIBTOMMATH_SRC}/tommath.h],
        ,
        AC_MSG_FAILURE([libtommath not found at "${LIBTOMMATH_SRC}"]))

# libtomcrypt source directory
AC_SUBST([LIBTOMCRYPT_SRC])
AC_ARG_WITH([libtomcryptsrc],
        AS_HELP_STRING([--with-libtomcryptsrc=@<:@path@:>@],
                [path to libtomcrypt source directory]),
                , [with_libtomcryptsrc=../third-party/libtomcrypt])
LIBTOMCRYPT_SRC=$[]with_libtomcryptsrc
AC_CHECK_FILE([${LIBTOMCRYPT_SRC}/src/headers/tomcrypt.h],
        ,
        AC_MSG_FAILURE([libtomcrypt not found at "${LIBTOMCRYPT_SRC}"]))

# EMHF app root directory
AC_SUBST([APP_ROOT])
AC_ARG_WITH([approot],
        AS_HELP_STRING([--with-approot=@<:@path@:>@],
                [path to EMHF app source directory]),
                , [with_approot=./app])
APP_ROOT=$[]with_approot
# AC_CONFIG_SUBDIRS fails silently on absolute paths
AS_IF([test "x${APP_ROOT:0:1}" == "x/"],
            AC_MSG_FAILURE([approot must be a relative path.]))
# make absolute
dnl AS_IF([test "x${APP_ROOT:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$APP_ROOT])

# EMHF app archive name
AC_SUBST([APP_ARCHIVE])
AC_ARG_WITH([apparchive],
        AS_HELP_STRING([--with-apparchive=@<:@name@:>@],
                [name of EMHF app archive (e.g., emhfapp.a)]),
                , [with_apparchive=emhfapp.a])
APP_ARCHIVE=$[]with_apparchive


AC_SUBST([EMHFCOREDIR])
AC_ARG_WITH([emhfcore],
        AS_HELP_STRING([--with-emhfcore=@<:@path@:>@],
                [path to NO emhfcore XXX FIXME app]),
                , [with_emhfcore=./emhfcore/x86])

#EMHF secondary app root directory
AC_SUBST([SECONDARYAPP_ROOT])
AC_ARG_WITH([secondaryapproot],
        AS_HELP_STRING([--with-secondaryapproot=@<:@path@:>@],
                [(optional) path to secondary EMHF app source directory]),
                , [with_secondaryapproot=])
SECONDARYAPP_ROOT=$[]with_secondaryapproot
# AC_CONFIG_SUBDIRS fails silently on absolute paths
AS_IF([test "x${SECONDARYAPP_ROOT:0:1}" == "x/"],
            AC_MSG_FAILURE([secondaryapproot must be a relative path.]))
# make absolute
dnl AS_IF([test "x${SECONDARYAPP_ROOT:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$SECONDARYAPP_ROOT])

# EMHF secondary app archive name
AC_SUBST([SECONDARYAPP_ARCHIVE])
AC_ARG_WITH([secondaryapparchive],
        AS_HELP_STRING([--with-secondaryapparchive=@<:@name@:>@],
                [(optional) name of secondary EMHF app archive (e.g., emhfsecapp.a)]),
                , [with_secondaryapparchive=emhfsecapp.a])
SECONDARYAPP_ARCHIVE=$[]with_secondaryapparchive




# todo- maybe test here if configured path actually has emhfcore in it
EMHFCOREDIR=$[]with_emhfcore
# make absolute
dnl AS_IF([test "x${EMHFCOREDIR:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$EMHFCOREDIR])

AC_SUBST([CMOCKDIR])
AC_ARG_WITH([cmock],
        AS_HELP_STRING([--with-cmock=@<:@path@:>@],
                [path to cmock]),
                , [with_cmock=../../../tools/cmock])
CMOCKDIR=$[]with_cmock

AC_SUBST([UNITYDIR])
AC_ARG_WITH([unity],
        AS_HELP_STRING([--with-unity=@<:@path@:>@],
                [path to unity]),
                , [with_unity=../../../tools/cmock/vendor/unity])
UNITYDIR=$[]with_unity

AC_SUBST([prefix])
AC_SUBST([exec_prefix])
AC_SUBST([datadir])
AC_SUBST([libdir])
AC_SUBST([includedir])
AC_SUBST([pkgdatadir], ['${datadir}/AC_PACKAGE_NAME'])
AC_SUBST([pkgconfigdir], ['${libdir}/pkgconfig'])
AC_SUBST([pkgincludedir], ['${includedir}/AC_PACKAGE_NAME'])

AC_CONFIG_SUBDIRS([${APP_ROOT}])
AC_CONFIG_SUBDIRS([${SECONDARYAPP_ROOT}])


AC_CONFIG_FILES([Makefile])
AC_OUTPUT
