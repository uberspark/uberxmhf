# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

include ../../devices/tv/svcmakefile.inc

TESTS=-DTEST_VMMCALL -DTEST_WITHOUTPARAM -DTEST_PARAM -DTEST_SEAL -DTEST_QUOTE

CFLAGS=$(SVC_CFLAGS) -g $(TESTS) -Wall -I../../tz/include -I../../devices/tv/common -I../../devices 
LDFLAGS=$(SVC_LDFLAGS)

# source .c file
SRCS = test.c pals.c 

# object files
OBJS = $(patsubst %.c, %.o, $(SRCS))

I_SOURCES = $(wildcard *.h)

all: test

test:$(OBJS) ../../tz/libtz.a ../../devices/tv/libsvcapi.a
	$(CC) $(LDFLAGS) -o $@ $(OBJS) ../../devices/tv/libsvcapi.a ../../tz/libtz.a

%.o:%.c $(I_SOURCES)
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D
