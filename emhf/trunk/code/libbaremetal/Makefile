# Makefile for libbaremetal
# author: amit vasudevan (amitvasudevan@acm.org)

# Builds a bunch of sublibraries

# TODO: Consider automating discovery of subdirs (presence of Makefile*?)
LIBDIRS = libtv_utpm libemhfcrypto libemhfutil libemhfc libtpm

# TODO: Tool settings; our project is not unique in this aspect

# FIXME- this should be configurable
export CFLAGS=-m32

.PHONY: all
all: subdirs

.PHONY: subdirs
subdirs: $(LIBDIRS)
	@for i in $(LIBDIRS); \
	do \
		(cd $$i && echo "Making all in $$i..." && $(MAKE) -w all) || exit 1; \
	done;
	$(AR) q libbaremetal.a libtv_utpm/libtv_utpm.a libemhfcrypto/libemhfcrypto.a libemhfutil/libemhfutil.a libemhfc/libemhfc.a libtpm/libtpm.a

.PHONY: clean
clean:
	@for i in $(LIBDIRS) ;\
	do \
		(cd $$i && echo "making clean in $$i..." && $(MAKE) -w clean) || exit 1; \
	done;
	$(RM) -rf libbaremetal.a
