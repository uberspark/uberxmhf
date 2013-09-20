AC_INIT([tee-sdk], [0.1], [jnewsome@cmu.edu])
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE([foreign -Wall -Werror])
AC_SUBST([CFLAGS], ['-g -O0 -m32'])
AC_PROG_CC
AC_CONFIG_HEADERS([include/config.h])

PKG_PROG_PKG_CONFIG
PKG_CHECK_MODULES([TRUSTVISOR], [trustvisor])


# install in-place by default
#AC_PREFIX_DEFAULT([${top_srcdir}/_install])
#svc_mk=$srcdir/../conf/svc.mk
#AC_SUBST([SVC_LINK_SCRIPT_SRC = $(srcdir)/conf/svc.ld
#AC_DEFUN([SVC_LINK_SCRIPT], [${pkgdatadir}/svc.ld])
AC_SUBST([datadir])
AC_SUBST([pkgdatadir], ['${datadir}/AC_PACKAGE_NAME'])
AC_SUBST([SVC_LINK_SCRIPT], ["${pkgdatadir}/svc.ld"])

# prevent gcc from compiling switch statements as jump tables. can
# probably get rid of this in the future by somehow ensuring that the
# jump table data is also included in the svc memory areas
#SVC_CFLAGS=-fno-jump-tables
# Not sure whether this is necessary. Carried over from an old makefile
#SVC_CFLAGS+=-fno-stack-protector
# use the designated linker script
#svc_ldflags=-T $(SVC_LINK_SCRIPT)

AC_CHECK_FUNCS([_aligned_malloc posix_memalign])

AC_CHECK_HEADERS([sys/mman.h sys/resource.h windows.h])
AC_CONFIG_FILES([Makefile src/Makefile include/Makefile dev/Makefile dev/tv/Makefile dev/tv/src/Makefile tee-sdk-app.pc tee-sdk-svc.pc dev/tv/tee-sdk-svc-tv.pc dev/tv/tee-sdk-app-tv.pc dev/tv/include/Makefile dev/null/Makefile dev/null/src/Makefile dev/null/tee-sdk-svc-null.pc])
AC_PROG_RANLIB
AC_OUTPUT
