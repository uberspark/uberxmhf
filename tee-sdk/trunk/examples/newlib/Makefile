# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

PROG_NAME=hello
PROG_OBJS=hello.o
CFLAGS+=-g -Wall
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv

PAL_NAME=hellopal
PAL_OBJS=hellopal.o pal-aux.o
PAL_CFLAGS+=-g -Wall
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv

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
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS)
.PHONY: clean all

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk
