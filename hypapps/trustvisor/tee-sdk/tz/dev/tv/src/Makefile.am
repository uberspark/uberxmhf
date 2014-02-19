# make these libraries are suitable for services to compile against

AM_CFLAGS = $(SVC_CFLAGS) @TRUSTVISOR_CFLAGS@

AM_CPPFLAGS = -I$(top_srcdir)/include -I$(srcdir)/../include

pkglib_LIBRARIES = libtz-tv.a libsvc-tv.a
libtz_tv_a_SOURCES = app_vmcalls.c scode.c tv.c tz_aligned_malloc.c
libsvc_tv_a_SOURCES = svc_vmcalls.c svc.c
