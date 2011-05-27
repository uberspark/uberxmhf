# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CFLAGS=-g -Wall
CPPFLAGS=$(TESTS)

# Get compile and link flags to compile against tv's
# app and svc back-ends. (the corresponding front-ends
# will be pulled in implicitly)
PKGCONFIG_DEPS=tee-sdk-svc-tv tee-sdk-app
PKG_CFLAGS=$(shell pkg-config --cflags $(PKGCONFIG_DEPS))
PKG_LDFLAGS=$(shell pkg-config --libs --static $(PKGCONFIG_DEPS))

CFLAGS+=$(PKG_CFLAGS)
LDFLAGS+=$(PKG_LDFLAGS)

# source .c file
SRCS = pal.c hello-newlib.c

# object files
OBJS = $(patsubst %.c, %.o, $(SRCS))

I_SOURCES = $(wildcard *.h)

all: hello-newlib

# FIXME - the static libraries should be proper dependencies, not in
# LDFLAGS. Using this rule with LDFLAGS coming last instead of first
# as in Make's default implicit rule is a partial workaround.  i.e.,
# we can link correctly, but Make won't know to rebuild if the
# static lib dependencies change.
hello-newlib:$(OBJS)
	$(CC) -o $@ $(OBJS) $(LDFLAGS) 

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D
