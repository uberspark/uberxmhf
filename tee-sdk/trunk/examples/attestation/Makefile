# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

PROG_NAME=attestation
CFLAGS=-g -Wall -Wextra -Werror
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libssl libcrypto json
PROG_OBJS=attestation.o json.o

PAL_NAME=pals
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv
PAL_OBJS=pals.o sha1.o
PAL_CFLAGS=-Wall -Wextra -Werror

# link pal against newlib
###### newlib paths. should make a pkg-config for this
NEWLIB=../../ports/newlib/install/i586
NEWLIB_LIBDIR=$(NEWLIB)/lib
NEWLIB_INCDIR=$(NEWLIB)/include
######
PAL_CFLAGS+=-I$(NEWLIB_INCDIR)
PAL_LDFLAGS+=-L$(NEWLIB_LIBDIR)
PAL_LDLIBS+=-lc -lnosys

all: $(PROG_NAME)

test:
	cd tests && $(MAKE) -w all

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* attestation attestation.D
	cd tests && $(MAKE) -w clean

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

