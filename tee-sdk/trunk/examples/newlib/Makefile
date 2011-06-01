# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

################## to go into global makefile
PAL_CFLAGS=$(shell pkg-config --cflags tee-sdk-svc tee-sdk-svc-tv)
PAL_LDFLAGS=-nostdlib -d -r
PAL_LDLIBS=$(shell pkg-config --libs --static tee-sdk-svc tee-sdk-svc-tv)
%.pal.o : LDLIBS = $(PAL_LDLIBS)
%.pal.o : CFLAGS = $(PAL_CFLAGS)
%.pal.o : LDFLAGS = $(PAL_LDFLAGS)
%.pal.ld: pal-template.ld
	sed 's/PAL_NAME/$*/g' pal-template.ld > $@
%.pal.o: %.o
	ld $(LDFLAGS) -o $@ $^ $(LDLIBS)
	objcopy -G $* $@
################### end global makefile

CFLAGS=-g -Wall

# Get compile and link flags to compile against tv's
# app back-end. (the corresponding front-end
# will be pulled in implicitly)
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv
PKG_CFLAGS=$(shell pkg-config --cflags $(PKGCONFIG_DEPS))
PKG_LDLIBS=$(shell pkg-config --libs --static $(PKGCONFIG_DEPS))

CFLAGS+=$(PKG_CFLAGS)
LDLIBS+=$(filter-out -T%,$(PKG_LDLIBS)) # we're not using the global link script


all: hello
OBJS = hello.o
I_SOURCES = $(wildcard *.h)

NEWLIB=../../ports/newlib/install/i586
NEWLIB_LIBDIR=$(NEWLIB)/lib
NEWLIB_INCDIR=$(NEWLIB)/include

PAL_NAME=hellopal

PAL_CFLAGS+=-g -Wall
PAL_CFLAGS+=-I$(NEWLIB_INCDIR)
PAL_LDFLAGS+=-L$(NEWLIB_LIBDIR)
PAL_LDLIBS+=-lc -lnosys
$(PAL_NAME).pal.o : hellopal.o pal-aux.o


#LDFLAGS+=-T$(PAL_NAME).ld
# XXX would be good to check for undefined symbols and warn\error 

# FIXME - the static libraries should be proper dependencies, not in
# LDFLAGS. Using this rule with LDFLAGS coming last instead of first
# as in Make's default implicit rule is a partial workaround.  i.e.,
# we can link correctly, but Make won't know to rebuild if the
# static lib dependencies change.
hello:$(OBJS) $(PAL_NAME).pal.o $(PAL_NAME).pal.ld
	$(CC) -T$(PAL_NAME).pal.ld $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS) 

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D
