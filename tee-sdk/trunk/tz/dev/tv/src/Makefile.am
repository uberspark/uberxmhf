# make these libraries are suitable for services to compile against

# FIXME hard-coding VMX for the moment. Need to make
# this an autoconf test, or better yet a runtime check
AM_CFLAGS = $(SVC_CFLAGS) -DIS_VMX

AM_CPPFLAGS = -I$(top_srcdir)/include -I$(srcdir)/../include

pkglib_LIBRARIES = libtz-tv.a libsvc-tv.a
libtz_tv_a_SOURCES = vmcalls.c scode.c tv.c
libsvc_tv_a_SOURCES = vmcalls.c
