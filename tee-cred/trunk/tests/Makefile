CMOCKDIR=../../../tools/cmock
CMOCKOBJ=$(CMOCKDIR)/src/cmock.o
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

CFLAGS=-Wall -Werror -g -DUSERSPACE_ONLY=1

SRCDIR=..

TEESDK_DATA_DIR=$(shell pkg-config --variable=pkgdatadir tee-sdk-app)
# pkgconfig helpers
include $(TEESDK_DATA_DIR)/pkgconfig.mk

CFLAGS+=$(call pkgconfig_cflags, tee-sdk-app tee-sdk-app-tv)
TEESDK_PKGINCLUDE_DIR=$(shell pkg-config --variable=includedir tee-sdk-app)/tee-sdk

all : mocks test

test : run_audit_tests run_audited-kv-pal_tests run_kv_tests run_audited-kv-pal-marshal_tests

mocks : mocks/Mockaudited-kv.c mocks/Mockaudit.c mocks/Mocktv.c mocks/Mocktz.c mocks/Mocksvcapi.c mocks/Mockaudited-kv-pal.o

audit_tests : audit_runner.o audit_tests.o audit.o $(UNITYOBJ)
PROGS+=audit_tests
OBJS+=audit_runner.o audit_tests.o audit.o

# tcm_tests : tcm_runner.o tcm_tests.o tcm.o mocks/Mockaudit.o mocks/Mockaudited-kv.o $(UNITYOBJ) $(CMOCKOBJ)
# PROGS+=tcm_tests
# OBJS+=tcm_runner.o tcm_tests.o tcm.o

# audited-kv_tests : audited-kv_runner.o audited-kv_tests.o audited-kv.o audited-kv-pal.o $(UNITYOBJ) $(CMOCKOBJ)
# audited-kv_tests : LDLIBS += $(call pkgconfig_ldlibs, tee-sdk-app tee-sdk-app-tv)
# audited-kv_tests : LDFLAGS += $(filter -L%, $(call pkgconfig_ldflags, tee-sdk-app tee-sdk-app-tv))
# PROGS+=audited-kv_tests
# OBJS+=audited-kv_runner.o audited-kv_tests.o audited-kv.o mocks/Mocktv.o

audited-kv-pal_tests : audited-kv-pal_runner.o audited-kv-pal_tests.o audited-kv-pal.o kv.o audited.o audited-kv-pal-globals.o $(UNITYOBJ) $(CMOCKOBJ)
audited-kv-pal_tests : LDLIBS += $(call pkgconfig_ldlibs, tee-sdk-svc tee-sdk-svc-tv) -lcrypto
audited-kv-pal_tests : LDFLAGS += $(filter -L%, $(call pkgconfig_ldflags, tee-sdk-svc tee-sdk-svc-tv))
PROGS+=audited-kv-pal_tests
OBJS+=audited-kv-pal_runner.o audited-kv-pal_tests.o audited-kv-pal.o kv.o

kv_tests: kv_runner.o kv_tests.o kv.o $(UNITYOBJ) $(CMOCKOBJ)
PROGS+=kv_tests
OBJS+=kv_runner.o kv_tests.o kv.o

audited-kv-pal-marshal_tests: audited-kv-pal-marshal_runner.o audited-kv-pal-marshal_tests.o audited-kv-pal-marshal.o audited-kv-pal.o kv.o audited.o mocks/Mocksvcapi.o audited-kv-pal-globals.o $(UNITYOBJ) $(CMOCKOBJ)
audited-kv-pal-marshal_tests : LDLIBS += $(call pkgconfig_ldlibs, tee-sdk-svc) -lcrypto
audited-kv-pal-marshal_tests : LDFLAGS += $(filter -L%, $(call pkgconfig_ldflags, tee-sdk-svc))
PROGS+=audited-kv-pal-marshal_tests
OBJS+=audited-kv-pal-marshal_runner.o audited-kv-pal-marshal_tests.o audited-kv-pal-marshal.o

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
test : CFLAGS+=-I$(CMOCKDIR)/src -I$(SRCDIR) -I./mocks
mocks/Mock%.c mocks/Mock%.h : $(SRCDIR)/%.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^
mocks/Mock%.o : mocks/Mock%.c
mocks/Mock%.o : CFLAGS+=-I$(SRCDIR) -I$(CMOCKDIR)/src -I$(UNITYDIR)/src -I$(TEESDK_PKGINCLUDE_DIR)

mocks/Mocktv.c : $(TEESDK_PKGINCLUDE_DIR)/tv.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^
mocks/Mocktz.c : $(TEESDK_PKGINCLUDE_DIR)/tz.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^
mocks/Mocksvcapi.c : $(TEESDK_PKGINCLUDE_DIR)/svcapi.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^

%.o : $(SRCDIR)/%.c
	$(CC) -c $(CPPFLAGS) $(CFLAGS) -o $@ $^
