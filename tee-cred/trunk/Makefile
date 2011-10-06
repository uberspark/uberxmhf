all : main

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

# create a separate object file for the reg program
# XXX not sure why I need to re-specify the recipe
proto-gend/db.pb-c-reg.o : proto-gend/db.pb-c.c
	$(CC) $(CPPCFLAGS) $(CFLAGS) -c $^ -o $@
proto-gend/audited.pb-c-reg.o : proto-gend/audited.pb-c.c
	$(CC) $(CPPCFLAGS) $(CFLAGS) -c $^ -o $@
proto-gend/akvp.pb-c-reg.o : proto-gend/akvp.pb-c.c
	$(CC) $(CPPCFLAGS) $(CFLAGS) -c $^ -o $@
proto-gend/storage.pb-c-reg.o : proto-gend/storage.pb-c.c
	$(CC) $(CPPCFLAGS) $(CFLAGS) -c $^ -o $@

PROG_NAME=main
PROG_OBJS= \
	audit.o \
	audited-kv.o \
	tcm.o \
	tze-pb-reg.o \
	audited-kv-pal-protos.o \
	proto-gend/db.pb-c-reg.o \
	proto-gend/audited.pb-c-reg.o \
	proto-gend/akvp.pb-c-reg.o
CFLAGS+=-g -Wall -Werror
LDFLAGS+=--static
CFLAGS+=-DUSERSPACE_ONLY=1
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libprotobuf-c

#PAL_BACKEND=tee-sdk-svc-tv
PAL_BACKEND=tee-sdk-svc-null
PAL_NAME=audited-kv-pal
PAL_OBJS= \
	audited-kv-pal.o \
	audited-kv-pal-marshal.o \
	kv.o \
	audited.o \
	audited-kv-pal-globals.o \
	audited-kv-pal-protos.o \
	tze-pb-svc.o \
	tze-pb-marshal.o \
	proto-gend/db.pb-c.o \
	proto-gend/audited.pb-c.o \
	proto-gend/akvp.pb-c.o \
	proto-gend/storage.pb-c.o
PAL_CFLAGS+=-g -Wall -Werror
PAL_PKGCONFIG_DEPS=tee-sdk-svc $(PAL_BACKEND) libcrypto libprotobuf-c

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
