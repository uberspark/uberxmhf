## Process this file with automake to generate Makefile.in

AUTOMAKE_OPTIONS = cygnus

INCLUDES = -I$(srcdir)/../include -I$(srcdir)/.. $(NEWLIB_CFLAGS) $(CROSS_CFLAGS) $(TARGET_CFLAGS)

GENERAL_SOURCES = netdb.c socket.c

#ELIX_4_SOURCES =

libnet_la_LDFLAGS =
libnet_la_CFLAGS =

if USE_LIBTOOL
noinst_LTLIBRARIES = libnet.la
libnet_la_SOURCES = $(GENERAL_SOURCES)
noinst_DATA = objectlist.awk.in
else
noinst_LIBRARIES = lib.a
lib_a_SOURCES = $(GENERAL_SOURCES)
lib_a_CFLAGS = $(AM_CFLAGS)
noinst_DATA =
endif # USE_LIBTOOL

include $(srcdir)/../../../../Makefile.shared

install-data-local:
	$(mkinstalldirs) $(DESTDIR)$(tooldir)/include/netinet; \
	for i in $(srcdir)/../include/netinet/*.h; do \
	  $(INSTALL_DATA) $$i $(DESTDIR)$(tooldir)/include/netinet/`basename $$i`; \
	done; \
	$(mkinstalldirs) $(DESTDIR)$(tooldir)/include/arpa; \
	for i in $(srcdir)/../include/arpa/*.h; do \
	  $(INSTALL_DATA) $$i $(DESTDIR)$(tooldir)/include/arpa/`basename $$i`; \
	done;
# $(mkinstalldirs) $(DESTDIR)$(tooldir)/include/net; \
# for i in $(srcdir)/../include/net/*.h; do \
#   $(INSTALL_DATA) $$i $(DESTDIR)$(tooldir)/include/net/`basename $$i`; \
# done;
# $(mkinstalldirs) $(DESTDIR)$(tooldir)/include/netinet6; \
# for i in $(srcdir)/../include/netinet6/*.h; do \
#   $(INSTALL_DATA) $$i $(DESTDIR)$(tooldir)/include/netinet6/`basename $$i`; \
# done; \
# $(mkinstalldirs) $(DESTDIR)$(tooldir)/include/netns; \
# for i in $(srcdir)/../include/netns/*.h; do \
#   $(INSTALL_DATA) $$i $(DESTDIR)$(tooldir)/include/netns/`basename $$i`; \
# done; \
# $(mkinstalldirs) $(DESTDIR)$(tooldir)/include/rpc; \
# for i in $(srcdir)/../include/rpc/*.h; do \
#   $(INSTALL_DATA) $$i $(DESTDIR)$(tooldir)/include/rpc/`basename $$i`; \
# done;
