CMOCKDIR=../../tools/cmock
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

all : test

test : run_audit_tests run_tcm_tests

audit_tests : audit_runner.o audit_tests.o audit.o $(UNITYOBJ)
PROGS+=audit_tests
OBJS+=audit_runner.o audit_tests.o audit.o $(UNITYOBJ)

tcm_tests : tcm_runner.o tcm_tests.o tcm.o $(UNITYOBJ)
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