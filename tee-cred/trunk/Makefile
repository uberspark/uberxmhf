CMOCKDIR=../../tools/cmock
CMOCKOBJ=$(CMOCKDIR)/src/cmock.o
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

CFLAGS=-Wall -Werror -g

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)
# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

CFLAGS+=$(call pkgconfig_cflags, tee-sdk-app tee-sdk-app-tv)
TEESDK_PKGINCLUDE_DIR=$(shell pkg-config --variable=includedir tee-sdk-app)/tee-sdk

all : mocks test

test : run_audit_tests run_tcm_tests run_audited-kv_tests run_audited-kv-pal_tests

mocks : mocks/Mockaudited-kv.c mocks/Mockaudit.c mocks/Mocktv.c

audit_tests : audit_runner.o audit_tests.o audit.o $(UNITYOBJ)
PROGS+=audit_tests
OBJS+=audit_runner.o audit_tests.o audit.o

tcm_tests : tcm_runner.o tcm_tests.o tcm.o mocks/Mockaudit.o mocks/Mockaudited-kv.o $(UNITYOBJ) $(CMOCKOBJ)
PROGS+=tcm_tests
OBJS+=tcm_runner.o tcm_tests.o tcm.o

audited-kv_tests : audited-kv_runner.o audited-kv_tests.o audited-kv.o mocks/Mocktv.o $(UNITYOBJ) $(CMOCKOBJ)
PROGS+=audited-kv_tests
OBJS+=audited-kv_runner.o audited-kv_tests.o audited-kv.o mocks/Mocktv.o

audited-kv-pal_tests : audited-kv-pal_runner.o audited-kv-pal_tests.o audited-kv-pal.o $(UNITYOBJ) $(CMOCKOBJ)
PROGS+=audited-kv-pal_tests
OBJS+=audited-kv-pal_runner.o audited-kv-pal_tests.o audited-kv-pal.o

clean:
	$(RM) $(PROGS) $(OBJS) mocks/*

test : CFLAGS+=-I$(UNITYDIR)/src -DUNITY_SUPPORT_64
# workaround to allow mocked header to include other tee-sdk headers
test : CFLAGS+=-I$(TEESDK_PKGINCLUDE_DIR)

### generic unity rules ###
run_%: %
	./$<
%_runner.c: %_tests.c
	ruby ${UNITYDIR}/auto/generate_test_runner.rb $< $@
### end generic unity rules ###
test : CFLAGS+=-I$(CMOCKDIR)/src -I. -I./mocks
mocks/Mock%.c mocks/Mock%.h : %.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^
mocks/Mock%.o : mocks/Mock%.c

mocks/Mocktv.c : $(TEESDK_PKGINCLUDE_DIR)/tv.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^

