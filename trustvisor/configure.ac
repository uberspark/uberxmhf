AC_INIT([trustvisor], [0.2])
#AC_CONFIG_AUX_DIR([build-aux]) # use this if\when switching to automake

AC_SUBST([prefix])
AC_SUBST([exec_prefix])
AC_SUBST([datadir])
AC_SUBST([libdir])
AC_SUBST([includedir])
AC_SUBST([pkgdatadir], ['${datadir}/AC_PACKAGE_NAME'])
AC_SUBST([pkgconfigdir], ['${libdir}/pkgconfig'])
AC_SUBST([pkgincludedir], ['${includedir}/AC_PACKAGE_NAME'])

AC_CONFIG_FILES([trustvisor.pc])
AC_OUTPUT

# libbaremetal source directory
AC_SUBST([LIBBAREMETAL_SRC])
AC_ARG_WITH([libbaremetalsrc],
        AS_HELP_STRING([--with-libbaremetalsrc=@<:@path@:>@],
                [path to libbaremetal source directory]),
                , [with_libbaremetalsrc=./libbaremetal])
LIBBAREMETAL_SRC=$[]with_libbaremetalsrc
# make absolute
dnl AS_IF([test "x${LIBBAREMETAL_SRC:0:1}" != "x/"],
dnl       [EMHFCOREDIR=$ac_abs_top_builddir/$LIBBAREMETAL_SRC])

