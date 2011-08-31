# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

#TESTS=-DTEST_VMMCALL -DTEST_WITHOUTPARAM -DTEST_PARAM -DTEST_SEAL -DTEST_LTSEAL -DTEST_QUOTE -DTEST_PCR_EXTEND -DTEST_PCR_READ -DTEST_RAND -DTEST_TIME -DTEST_NV_ROLLBACK
TESTS=-DTEST_NV_ROLLBACK

PROG_NAME=test
CFLAGS=-g -Wall -Wextra -Werror
CPPFLAGS=$(TESTS)
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libssl libcrypto
PROG_OBJS=test.o

PAL_NAME=pals
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv
PAL_OBJS=pals.o
PAL_CFLAGS=-Wall -Wextra -Werror

all: $(PROG_NAME)

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk

