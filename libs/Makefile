# Makefile for libbaremetal
# author: amit vasudevan (amitvasudevan@acm.org)

# Builds a bunch of sublibraries

# get the "source" directory of this Makefile (useful for
# out-of-tree build)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

# grab all the sub-library directories
LIBDIRS = $(wildcard $(srcdir)/lib*)
LIBDIRSRELATIVE := $(patsubst $(srcdir)/%, %, $(LIBDIRS))


LIBBAREMETAL_OBJECTS_DIR = _objs_libbaremetal

.PHONY: all
all: subdirs

.PHONY: subdirs
subdirs: $(LIBDIRS)
	mkdir -p $(LIBBAREMETAL_OBJECTS_DIR)
	@for i in $(LIBDIRS); \
	do \
		(cd $(LIBBAREMETAL_OBJECTS_DIR) &&	echo "Making all in $$i..." && $(MAKE) -f $$i/Makefile -w all) || exit 1; \
	done;
	@for i in $(LIBDIRSRELATIVE); \
	do \
		(cd $(LIBBAREMETAL_OBJECTS_DIR)/_objs_$$i && ar -rcs ../libbaremetal.a *.o) || exit 1; \
	done;

.PHONY: clean
clean:
	rm -rf $(LIBBAREMETAL_OBJECTS_DIR)
