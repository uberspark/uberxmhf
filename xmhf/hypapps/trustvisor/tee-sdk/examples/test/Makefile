# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

TESTS=
TESTS+=-DTEST_VMMCALL
TESTS+=-DTEST_WITHOUTPARAM
TESTS+=-DTEST_PARAM
TESTS+=-DTEST_SEAL
TESTS+=-DTEST_LTSEAL
TESTS+=-DTEST_QUOTE
TESTS+=-DTEST_PCR_EXTEND
TESTS+=-DTEST_PCR_READ
TESTS+=-DTEST_RAND
TESTS+=-DTEST_TIME
#TESTS+=-DTEST_NV_ROLLBACK

# Set to 1 to use 'null' backend and test in userspace
# Set to 0 to use TrustVisor backend and run 'for real'
DO_USERSPACE_ONLY=0

ifeq ($(MINGW), 1)
	CROSS=i686-pc-mingw32-
endif
PKG_CONFIG=pkg-config
CC:=gcc
LD:=ld
NM:=nm
OBJCOPY:=objcopy
CC:=$(CROSS)$(CC)
LD:=$(CROSS)$(LD)
NM:=$(CROSS)$(NM)
PKG_CONFIG:=$(CROSS)$(PKG_CONFIG)
OBJCOPY:=$(CROSS)$(OBJCOPY)

PROG_NAME=test
CFLAGS=-g -Wall -Wextra -Werror
ifeq ($(MINGW), 1)
	# workaround - mingw's format string checking is buggy,
	# leading to false warnings, which get upgraded to errors
	CFLAGS += -Wno-format
endif

CFLAGS+=-DUSERSPACE_ONLY=$(DO_USERSPACE_ONLY)
CFLAGS+=-m32
LDFLAGS=-m32 -L/usr/lib32
CPPFLAGS=$(TESTS)
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libssl libcrypto
PROG_OBJS=test.o

# Set the backend appropriately based on desire for userspace testing
ifeq ($(DO_USERSPACE_ONLY), 1)
	PAL_BACKEND=tee-sdk-svc-null
else
	PAL_BACKEND=tee-sdk-svc-tv
endif

PAL_NAME=pals
PAL_PKGCONFIG_DEPS=tee-sdk-svc $(PAL_BACKEND)
PAL_OBJS=pals.o
PAL_CFLAGS=-Wall -Wextra -Werror -m32
PAL_LDFLAGS=-m32

.PHONY: all
all: $(PROG_NAME) Makefile

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D

TEESDK_DATA_DIR=$(shell $(PKG_CONFIG) --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

