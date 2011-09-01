all : test

test :
	cd tests ; make
.PHONY : test

PROG_NAME=main
PROG_OBJS=audit.o audited-kv.o tcm.o
CFLAGS+=-g -Wall -Werror
# CFLAGS+=-DUSERSPACE_ONLY=1
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv

PAL_BACKEND=tee-sdk-svc-tv
# PAL_BACKEND=tee-sdk-svc-null
PAL_NAME=audited-kv-pal
PAL_OBJS=audited-kv-pal.o audited-kv-pal-marshal.o kv.o audited.o audited-kv-pal-globals.o
PAL_CFLAGS+=-g -Wall -Werror
PAL_PKGCONFIG_DEPS=tee-sdk-svc $(PAL_BACKEND) libcrypto

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
