## Process this file with automake to generate Makefile.in

AUTOMAKE_OPTIONS = cygnus

INCLUDES = -I$(srcdir)/../include -I$(srcdir)/.. $(NEWLIB_CFLAGS) $(CROSS_CFLAGS) $(TARGET_CFLAGS)

noinst_LIBRARIES = lib.a
lib_a_SOURCES = cbuf.c write.c
lib_a_CFLAGS = $(AM_CFLAGS)
noinst_DATA =

include $(srcdir)/../../../../Makefile.shared
