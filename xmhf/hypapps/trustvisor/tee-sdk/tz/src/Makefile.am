# make this library suitable for services to compile against
AM_CFLAGS = $(SVC_CFLAGS)

AM_CPPFLAGS = -I$(top_srcdir)/include 

pkglib_LIBRARIES = libtz.a libsvc.a
libtz_a_SOURCES = marshal.c tz.c tze.c ../include/tzmarshal.h ../include/tz.h ../include/tze.h ../include/list.h

libsvc_a_SOURCES = marshal.c ../include/tzmarshal.h ../include/tz.h ../include/list.h
