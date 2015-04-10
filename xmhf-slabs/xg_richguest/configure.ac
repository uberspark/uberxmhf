AC_INIT([xmhfgeecslab], [1.0.0])
AC_CONFIG_AUX_DIR([build-aux]) # use this if\when switching to automake

AC_PROG_INSTALL


# simple configuration of tools. (just looks for matching binary
# on PATH)
#AC_CHECK_PROG([CC], [gcc], [gcc])
AC_CHECK_PROG([CC], [clang], [clang])
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

# user-defined options

# slab type
AC_SUBST([SLABTYPE])
AC_ARG_WITH([slabtype],
        AS_HELP_STRING([--with-slabtype=@<:@TYPE@:>@],
                [select slab type (tprimeslab, tprogslab, uprogslab, ugprogslab)]),
                , [with_slabtype=ugprogslab])
SLABTYPE=$[]with_slabtype


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
