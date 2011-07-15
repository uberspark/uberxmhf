all: secret-fun.bin load-code seal-code

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk
# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

PAL_NAME=sealed-code-pal
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv
PAL_OBJS=sealed-code-pal.o

PROG_NAME=seal-code
CFLAGS=-g -Wall
LDLIBS=-ltz -ltz-tv
LDFLAGS=
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv
PROG_OBJS=sealed-code-pal-interface.o common.o seal-code.o 
# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

PROG_NAME=load-code
CFLAGS=-g -Wall
LDLIBS=-ltz -ltz-tv
LDFLAGS=
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv
PROG_OBJS=sealed-code-pal-interface.o common.o load-code.o
# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

secret-fun: secret-fun.c
	$(CC) --static -fPIC -nostdlib -o $@ $? -Wall
secret-fun.bin: secret-fun
	objcopy -O binary -j .text -j .rodata ./secret-fun secret-fun.bin

.PHONY: clean
clean:
	$(RM) *.o seal-code load-code secret-fun secret-fun.bin
