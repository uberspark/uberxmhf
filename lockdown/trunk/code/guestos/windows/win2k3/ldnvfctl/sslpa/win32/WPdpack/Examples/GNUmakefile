# Makefile for cygwin gcc
# Nate Lawson <nate@rootlabs.com>

SUBDIRS = PKTDUMP TG TestApp pcap_filter

all clean install uninstall: ${SUBDIRS}
	for subdir in ${SUBDIRS}; do \
		echo "Entering $$subdir"; \
		(cd $$subdir && ${MAKE} $@) \
	done;
