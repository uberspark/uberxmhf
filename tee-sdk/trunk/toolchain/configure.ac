AC_INIT([tsvc-toolchain], [0.1])
AC_CONFIG_AUX_DIR([build-aux])
AC_CANONICAL_SYSTEM

AS_IF([test -z ${target}],
            target_cpu=i586;
            target_os=tsvc;
            target="${target_cpu}-${target_os}"
            target_alias=$target)
AC_SUBST([target_cpu])
AC_SUBST([target_os])
AC_SUBST([target_alias])

AS_IF([test -z ${SYSROOT}],
            SYSROOT='${prefix}'/${target_alias})           
AC_SUBST([SYSROOT])

#AC_SUBST([exec_prefix], [$prefix/$ARCH-$OS/bin]) # wrappers get installed here
#AC_SUBST([datadir])
#AC_SUBST([libdir])
#AC_SUBST([includedir])

# we want these to be absolute for substitution
# into the wrapper scripts

AS_IF([test "$host" != "$build"],
      [TOOLPREFIX="${host_alias}-"],
      [TOOLPREFIX=""])

AC_PATH_PROG([AR], [${TOOLPREFIX}ar])
AC_PATH_PROG([AS], [${TOOLPREFIX}as])
AC_PATH_PROG([CC], [${TOOLPREFIX}cc])
AC_PATH_PROG([LD], [${TOOLPREFIX}ld])
AC_PATH_PROG([NM], [${TOOLPREFIX}nm])
AC_PATH_PROG([OBJDUMP], [${TOOLPREFIX}objdump])
AC_PATH_PROG([RANLIB], [${TOOLPREFIX}ranlib])
AC_PATH_PROG([STRIP], [${TOOLPREFIX}strip])
AC_PATH_PROG([PKG_CONFIG], [${TOOLPREFIX}pkg-config])

AC_SUBST([CCLIB], [`$CC -m32 --print-file-name=`])

AC_SUBST([LDFLAGS])
LDFLAGS=""
LDFLAGS="$LDFLAGS -nostdlib"
LDFLAGS="$LDFLAGS -L"'$prefix'"/$target_alias/usr/local/lib -L"'$prefix'"/$target_alias/usr/lib -L"'$prefix'"/$target_alias/lib"
LDFLAGS="$LDFLAGS -L$CCLIB"

AC_SUBST([LDLIBS])
LDLIBS="-lgcc -lc -lnosys"

AC_SUBST([CCINC], [`$CC --print-file-name=include`])

AC_SUBST([CFLAGS])
CFLAGS="-march=$target_cpu"
CFLAGS="$CFLAGS -nostdinc" # drop default include directories
CFLAGS="$CFLAGS -isystem $CCINC -isystem $CCINC-fixed" # add back compiler-include directories
CFLAGS="$CFLAGS -I"'$prefix'"/$target_alias/usr/local/include -I"'$prefix'"/$target_alias/usr/include -I"'$prefix'"/$target_alias/include"
#CFLAGS="$CFLAGS --sysroot=$prefix" # would replace the above nastiness, but unfortunately ld is not built to support it on ubuntu
CFLAGS="$CFLAGS -fno-jump-tables" # sometimes conflicts with PAL memory protections. may no longer be needed
CFLAGS="$CFLAGS -fno-stack-protector" # stack protector results in unresolved symbols

case $host_os in
  *cygwin* ) CYGWIN=yes;;
         * ) CYGWIN=no;;
esac
AS_IF([test "x${CYGWIN}" != "xno"],
  # lie to newlib so it doesn't try including cygwin system headers
  CFLAGS="$CFLAGS -U__CYGWIN__ -U__CYGWIN32__";
  # ugly hack to pick up __main, allowing cc to compile
  # standalone executables, even if they won't run. this is
  # helpful to fool autoconf when cross-compiling
  LDLIBS="$LDLIBS /usr/lib/libcygwin.a",
  )

# unfortunately there's no command-line option to the compiler to specify
# which linker to use, in which case we could just point it to our linker
# wrapper that has the appropriate linker flags. Since we can't do that,
# we need to also pass the linker flags to the compiler for when the
# compiler is used as a wrapper to the linker.
#CFLAGS="$CFLAGS $LDFLAGS"

AC_CHECK_PROG([RM], [rm -f], [rm -f])
AC_CHECK_PROG([CP], [cp], [cp])
AC_CHECK_PROG([SED], [sed], [sed])
AC_CHECK_PROG([CAT], [cat], [cat])
AC_CHECK_PROG([INSTALL], [install], [install])

AC_PROG_INSTALL

AC_CONFIG_FILES([
  ar as cc ld nm objdump ranlib strip pkg-config Makefile
])
AC_OUTPUT
