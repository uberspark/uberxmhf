CMOCKDIR=../../tools/cmock
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

all : test

test : run_audit_tests
test : CFLAGS+=-I$(UNITYDIR)/src

audit_tests : audit_runner.o audit_tests.o audit.o $(UNITYOBJ)

run_%: %
	./$<

%_runner.c: %_tests.c
	ruby ${UNITYDIR}/auto/generate_test_runner.rb $< $@