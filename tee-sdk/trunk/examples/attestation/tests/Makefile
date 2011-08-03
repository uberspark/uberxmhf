CMOCKDIR=../../../../../tools/cmock
CMOCKOBJ=$(CMOCKDIR)/src/cmock.o
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv libssl libcrypto json

CFLAGS += -I${UNITYDIR}/src -DUNITY_SUPPORT_64 -g
CFLAGS := $(filter-out -nostdinc,${CFLAGS})

LDFLAGS += -lssl -lcrypto -ljson

all: do_test

# FIXME should create separately compiled objects here, instead of in src dir
#unity.o: ${UNITYDIR}/src/unity.c
#pt.o: ../app/pt.c

test: test_runner.o test.o ../common.o ${UNITYDIR}/src/unity.o
	$(CC) -o $@ $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS)

do_%: %
	./$<

%_runner.c: %.c
	ruby ${UNITYDIR}/auto/generate_test_runner.rb $< $@



#-------------------------------------------------------------------------------
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) *.o *~
	$(RM) *_runner.c
	$(RM) ../app/*.o

#-------------------------------------------------------------------------------
TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)

# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

# rules for compiling pal intermediate objects
include $(TEESDK_DATA_DIR)/pal.mk

# rules for compiling a program PROG_NAME that uses one pal PAL_NAME
include $(TEESDK_DATA_DIR)/onepal.mk
