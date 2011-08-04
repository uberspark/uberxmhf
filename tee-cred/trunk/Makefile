all : test

test :
	cd tests ; make
.PHONY : test

PROG_NAME=main
PROG_OBJS=audit.o audited-kv.o tcm.o
CFLAGS+=-g -Wall -Werror
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv

PAL_NAME=audited-kv-pal
PAL_OBJS=audited-kv-pal.o audited-kv-pal-marshal.o kv.o
PAL_CFLAGS+=-g -Wall -Werror
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv

# link pal against openssl
OPENSSL=../../tee-sdk/trunk/ports/openssl/install
PAL_CFLAGS+=-I$(OPENSSL)/include
PAL_LDFLAGS+=-L$(OPENSSL)/lib
PAL_LDLIBS+=-lcrypto

# link pal against newlib
###### newlib paths. should make a pkg-config for this
NEWLIB=../../tee-sdk/trunk/ports/newlib/install/i586-tsvc
NEWLIB_LIBDIR=$(NEWLIB)/lib
NEWLIB_INCDIR=$(NEWLIB)/include
######
PAL_CFLAGS+=-I$(NEWLIB_INCDIR)
PAL_LDFLAGS+=-L$(NEWLIB_LIBDIR)
PAL_LDLIBS+=-lc -lnosys

all: $(PROG_NAME)
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS)
	cd tests ; make clean
.PHONY: clean all

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk
