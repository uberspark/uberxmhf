srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
VPATH=$(srcdir)

all : depend main FORCE

FORCE:
.PHONY : FORCE

test : FORCE
	cd tests ; make

# trick for creating object directories without having
# a dependency on the directory itself (which is modified every
# time a file is created inside it)
%/.d:
	mkdir -p $(@D)
	touch $@
.PRECIOUS: %/.d

proto-gend/%.pb-c.c proto-gend/%.pb-c.h : %.proto $(CURDIR)/proto-gend/.d
	protoc-c --c_out=proto-gend --proto_path=$(srcdir) $<

#CROSS=
CROSS=i686-pc-mingw32-
PKG_CONFIG=pkg-config
CC:=gcc
LD:=ld
main: CC:=$(CROSS)$(CC)
main: LD:=$(CROSS)$(LD)
main: PKG_CONFIG:=$(CROSS)$(PKG_CONFIG)

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
#CFLAGS+=-g -Wall -Werror -I.
CFLAGS+=-g -Wall -I.
LDFLAGS+=--static
CFLAGS+=-DUSERSPACE_ONLY=1
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libprotobuf-c gtk+-2.0

#PAL_BACKEND=tee-sdk-svc-tv
PAL_BACKEND=tee-sdk-svc-null
PAL_NAME=audited-kv-pal
PAL_OBJS_BARE= \
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
PAL_OBJS=$(addprefix pal-build/, $(PAL_OBJS_BARE))
PAL_CFLAGS+=-g -Wall -Werror -I. -UWINDOWS -UWIN32 -U_WIN32

pal-build/%.o : %.c $(CURDIR)/pal-build/proto-gend/.d
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

%.pal.o: pal-build/%.o
	$(CC) -r -Wl,-d $(LDFLAGS) -o $@ $^ $(LDLIBS)
	objcopy -G $(subst -,_,$*) $@
	if test `nm -u $@ | wc -l` -ne 0 ; then echo "undefd symbols in $@:"; nm -u $@; rm $@; false; else true; fi

PAL_PKGCONFIG_DEPS=tee-sdk-svc $(PAL_BACKEND) libcrypto libprotobuf-c

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

all: $(PROG_NAME)

clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS) $(PAL_OBJS) .depend .paldepend proto-gend/*.pb-c.[ch]
	cd tests ; make clean
.PHONY: clean all

SRCS=$(patsubst %.o,%.c,$(PROG_OBJS))
depend: .depend
.depend: $(SRCS)
	$(CC) $(CFLAGS) -MM $^ > $@ ; if [ $$? -ne 0 ] ; then rm $@ ; fi
include .depend

PAL_SRCS=$(patsubst %.o,%.c,$(PAL_OBJS_BARE))
paldepend: .paldepend
.paldepend: $(PAL_SRCS)
	$(PAL_CC) $(CFLAGS) -MM $^ > $@ ; if [ $$? -ne 0 ] ; then rm $@ ; fi
include .paldepend

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

