AC_INIT([emhf], [0.2])
#AC_CONFIG_AUX_DIR([build-aux]) # use this if\when switching to automake

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

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
