CMOCKDIR=../../tools/cmock
CMOCKOBJ=$(CMOCKDIR)/src/cmock.o
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

CFLAGS=-Wall

all : test

test : run_audit_tests run_tcm_tests

audit_tests : audit_runner.o audit_tests.o audit.o $(UNITYOBJ)
PROGS+=audit_tests
OBJS+=audit_runner.o audit_tests.o audit.o $(UNITYOBJ)

tcm_tests : tcm_runner.o tcm_tests.o tcm.o mocks/Mockaudit.o $(UNITYOBJ) $(CMOCKOBJ)
PROGS+=tcm_tests
OBJS+=tcm_runner.o tcm_tests.o tcm.o $(UNITYOBJ)

clean:
	$(RM) $(PROGS) $(OBJS)

### generic unity rules ###
test : CFLAGS+=-I$(UNITYDIR)/src
run_%: %
	./$<
%_runner.c: %_tests.c
	ruby ${UNITYDIR}/auto/generate_test_runner.rb $< $@
### end generic unity rules ###
test : CFLAGS+=-I$(CMOCKDIR)/src -I. -I./mocks
mocks/Mock%.c mocks/Mock%.h : %.h
	ruby $(CMOCKDIR)/lib/cmock.rb -ocmockConfig.yml $^