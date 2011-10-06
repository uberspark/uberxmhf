srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
VPATH=$(srcdir)

# we want to look in main source directory for .c files, but *not*
# object files, which must be compiled separately for the pal
vpath %.c $(srcdir)/..

all : audited-kv-pal.pal.o

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
	audited-kv-pal-storage.o \
	proto-gend/db.pb-c.o \
	proto-gend/audited.pb-c.o \
	proto-gend/akvp.pb-c.o \
	proto-gend/storage.pb-c.o

#PAL_OBJS=$(addprefix pal-build/, $(PAL_OBJS_BARE))
PAL_CFLAGS+=-g -Wall -Werror
PAL_PKGCONFIG_DEPS=tee-sdk-svc $(PAL_BACKEND) libcrypto libprotobuf-c

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

clean:
	$(RM) $(PAL_OBJS) audited-kv-pal.pal.o
.PHONY: clean

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

