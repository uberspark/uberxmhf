srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
VPATH=$(srcdir)

all : main

pal-build/audited-kv-pal.pal.o :
	cd pal-build ; make audited-kv-pal.pal.o

test :
	cd tests ; make
.PHONY : test

proto-gend/db.pb-c.c proto-gend/db.pb-c.h : db.proto
	protoc-c --c_out=proto-gend db.proto

proto-gend/audited.pb-c.c proto-gend/audited.pb-c.h : audited.proto
	protoc-c --c_out=proto-gend audited.proto

proto-gend/akvp.pb-c.c proto-gend/akvp.pb-c.h : akvp.proto
	protoc-c --c_out=proto-gend akvp.proto

proto-gend/storage.pb-c.c proto-gend/storage.pb-c.h : storage.proto
	protoc-c --c_out=proto-gend storage.proto

PROG_NAME=main
PAL_NAME=audited-kv-pal
PROG_OBJS= \
	audit.o \
	audited-kv.o \
	tcm.o \
	tze-pb-reg.o \
	audited-kv-pal-protos.o \
	proto-gend/db.pb-c.o \
	proto-gend/audited.pb-c.o \
	proto-gend/akvp.pb-c.o \
	proto-gend/storage.pb-c.o
CFLAGS+=-g -Wall -Werror
LDFLAGS+=--static
CFLAGS+=-DUSERSPACE_ONLY=1
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libprotobuf-c
CFLAGS+=$(call pkgconfig_cflags, $(PKGCONFIG_DEPS))
LDLIBS+=$(call pkgconfig_ldlibs, $(PKGCONFIG_DEPS))
LDFLAGS+=$(call pkgconfig_ldflags, $(PKGCONFIG_DEPS))
LDLIBS+=-T$(PAL_NAME).pal.ld

# generate a pal-specific linker script
$(PAL_NAME).pal.ld :
	sed 's/PAL_NAME/pal-build\/$(PAL_NAME)/g' $(TEESDK_DATA_DIR)/pal-template.ld > $@

$(PROG_NAME) : $(PROG_OBJS) $(PAL_NAME).pal.ld
	$(CC) $(LDFLAGS) -o $@ $(PROG_OBJS) $(LDLIBS)

all: $(PROG_NAME)

clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS)
	cd tests ; make clean
	cd pal-build ; make clean
.PHONY: clean all

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

