srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
VPATH=$(srcdir)

all : depend main

FORCE:
.PHONY : FORCE

test :
	cd tests ; make
.PHONY : test

proto-gend/%.pb-c.c proto-gend/%.pb-c.h : %.proto
	protoc-c --c_out=proto-gend $^

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
SRCS=$(patsubst %.o,%.c,$(PROG_OBJS))
CFLAGS+=-g -Wall -Werror
LDFLAGS+=--static
#CFLAGS+=-DUSERSPACE_ONLY=1
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libprotobuf-c
CFLAGS+=$(call pkgconfig_cflags, $(PKGCONFIG_DEPS))
LDLIBS+=$(call pkgconfig_ldlibs, $(PKGCONFIG_DEPS))
LDFLAGS+=$(call pkgconfig_ldflags, $(PKGCONFIG_DEPS))
LDLIBS+=-T$(PAL_NAME).pal.ld

pal-build/$(PAL_NAME).pal.o : FORCE
	cd pal-build ; make $(PAL_NAME).pal.o
$(PAL_NAME).pal.ld :
	sed 's/PAL_NAME/pal-build\/$(PAL_NAME)/g' $(TEESDK_DATA_DIR)/pal-template.ld > $@

$(PROG_NAME) : $(PROG_OBJS) $(PAL_NAME).pal.ld pal-build/$(PAL_NAME).pal.o
	$(CC) $(LDFLAGS) -o $@ $(PROG_OBJS) $(LDLIBS)

all: $(PROG_NAME)

clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS) .depend
	cd tests ; make clean
	cd pal-build ; make clean
.PHONY: clean all

depend: .depend
.depend: $(SRCS)
	rm -f ./.depend
	$(CC) $(CFLAGS) -MM $^ >> ./.depend;
include .depend

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

