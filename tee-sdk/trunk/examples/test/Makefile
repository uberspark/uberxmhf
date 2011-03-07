# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

TESTS=-DTEST_VMMCALL -DTEST_WITHOUTPARAM -DTEST_PARAM -DTEST_SEAL -DTEST_QUOTE

CFLAGS=-g -Wall
CPPFLAGS=$(TESTS)

PKGCONFIG_DEPS=tee-sdk-svc-tv tee-sdk-app-tv
PKG_CFLAGS=$(shell pkg-config --cflags $(PKGCONFIG_DEPS))
PKG_LDFLAGS=$(shell pkg-config --libs --static $(PKGCONFIG_DEPS))

CFLAGS+=$(PKG_CFLAGS)
LDFLAGS+=$(PKG_LDFLAGS)

# source .c file
SRCS = test.c pals.c 

# object files
OBJS = $(patsubst %.c, %.o, $(SRCS))

I_SOURCES = $(wildcard *.h)

all: test

test:$(OBJS)
	@echo $(PKG_CFLAGS)
	@echo $(PKG_LDFLAGS)
	$(CC) -o $@ $(OBJS) $(LDFLAGS) 

%.o:%.c $(I_SOURCES)
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D
