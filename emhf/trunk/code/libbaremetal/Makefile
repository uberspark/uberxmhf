# Makefile for libbaremetal
# author: amit vasudevan (amitvasudevan@acm.org)

# Builds a bunch of sublibraries

# TODO: Consider automating discovery of subdirs (presence of Makefile*?)
#LIBDIRS = libtv_utpm libemhfcrypto libemhfutil libemhfc libtpm

# get the "source" directory of this Makefile (useful for
# out-of-tree build)
srcdir := $(dir $(lastword $(MAKEFILE_LIST)))

# grab all the sub-library directories
LIBDIRS = $(wildcard $(srcdir)lib*)

# TODO: Tool settings; our project is not unique in this aspect

# FIXME- this should be configurable
#export CFLAGS=-m32

.PHONY: all
all: subdirs

.PHONY: subdirs
subdirs: $(LIBDIRS)
	mkdir -p _objects
	@for i in $(LIBDIRS); \
	do \
		#(cd $$i && echo "Making all in $$i..." && $(MAKE) -w all) || exit 1; \
		(cd _objects &&	echo "Making all in $$i..." && $(MAKE) -f ../$$i/Makefile -w all) || exit 1; \
	done;
	cd _objects && ar -rcs libbaremetal.a *.o
	
.PHONY: clean
clean:
	mkdir -p _objects
	@for i in $(LIBDIRS) ;\
	do \
		#(cd $$i && echo "making clean in $$i..." && $(MAKE) -w clean) || exit 1; \
		(cd _objects && echo "making clean in $$i..." && $(MAKE) -f ../$$i/Makefile -w clean) || exit 1; \
	done;
	rm -rf _objects
