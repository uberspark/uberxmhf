AC_INIT([tsvc-toolchain], [0.1])

AC_SUBST([ARCH], ['i586'])
AC_SUBST([OS], ['tsvc'])
AC_SUBST([SYSROOT], ['$prefix'/$ARCH-$OS])

#AC_SUBST([prefix], [/usr/local])
#AC_SUBST([exec_prefix], [$prefix/$ARCH-$OS/bin]) # wrappers get installed here
#AC_SUBST([datadir])
#AC_SUBST([libdir])
#AC_SUBST([includedir])

# we want these to be absolute for substitution
# into the wrapper scripts
AC_PATH_PROG([AR], [ar], [ar])
AC_PATH_PROG([AS], [as], [as])
AC_PATH_PROG([CC], [cc], [cc])
AC_PATH_PROG([LD], [ld], [ld])
AC_PATH_PROG([NM], [nm], [nm])
AC_PATH_PROG([OBJDUMP], [objdump], [objdump])
AC_PATH_PROG([RANLIB], [ranlib], [ranlib])
AC_PATH_PROG([STRIP], [strip], [strip])
AC_PATH_PROG([PKG_CONFIG], [pkg-config], [pkg-config])

AC_SUBST([CCLIB], [`$CC --print-file-name=`])

AC_SUBST([LDFLAGS])
LDFLAGS=""
LDFLAGS="$LDFLAGS -nostdlib"
LDFLAGS="$LDFLAGS -L"'$prefix'"/$ARCH-$OS/usr/local/lib -L"'$prefix'"/$ARCH-$OS/usr/lib -L"'$prefix'"/$ARCH-$OS/lib"
LDFLAGS="$LDFLAGS -L$CCLIB"

AC_SUBST([LDLIBS])
LDLIBS="-lgcc -lc -lnosys"

AC_SUBST([CCINC], [`$CC --print-file-name=include`])

AC_SUBST([CFLAGS])
CFLAGS="-march=$ARCH"
CFLAGS="$CFLAGS -nostdinc" # drop default include directories
CFLAGS="$CFLAGS -isystem $CCINC -isystem $CCINC-fixed" # add back compiler-include directories
CFLAGS="$CFLAGS -I"'$prefix'"/$ARCH-$OS/usr/local/include -I"'$prefix'"/$ARCH-$OS/usr/include -I"'$prefix'"/$ARCH-$OS/include"
#CFLAGS="$CFLAGS --sysroot=$prefix" # would replace the above nastiness, but unfortunately ld is not built to support it on ubuntu
CFLAGS="$CFLAGS -fno-jump-tables" # sometimes conflicts with PAL memory protections. may no longer be needed
CFLAGS="$CFLAGS -fno-stack-protector" # stack protector results in unresolved symbols

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

AC_CONFIG_FILES([
  ar as cc ld nm objdump ranlib strip pkg-config Makefile
])
AC_OUTPUT