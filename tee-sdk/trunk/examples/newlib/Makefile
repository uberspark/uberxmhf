# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

################## generic pal-building rules
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv
PAL_CFLAGS=$(shell pkg-config --cflags $(PAL_PKGCONFIG_DEPS))
PAL_LDFLAGS=-nostdlib -d -r
# XXX temporarily manually filtering out the old linker script here
PAL_LDLIBS=$(filter-out -T%, \
	$(shell pkg-config --libs --static $(PAL_PKGCONFIG_DEPS)))
%.pal.o : LDLIBS = $(PAL_LDLIBS)
%.pal.o : CFLAGS = $(PAL_CFLAGS)
%.pal.o : LDFLAGS = $(PAL_LDFLAGS)
%.pal.ld: pal-template.ld
	sed 's/PAL_NAME/$*/g' pal-template.ld > $@
%.pal.o: %.o
	ld $(LDFLAGS) -o $@ $^ $(LDLIBS)
	objcopy -G $* $@
# XXX would be good to check for undefined symbols and warn\error 
################### end global makefile

###### newlib paths. should make a pkg-config for this
NEWLIB=../../ports/newlib/install/i586
NEWLIB_LIBDIR=$(NEWLIB)/lib
NEWLIB_INCDIR=$(NEWLIB)/include
######

# regular program target
all: hello

### PAL rules

# PAL target
PAL_NAME=hellopal
PAL_OBJS=hellopal.o pal-aux.o
$(PAL_NAME).pal.o : $(PAL_OBJS)

# extra flags for PAL
PAL_CFLAGS+=-g -Wall

# link pal against newlib
PAL_CFLAGS+=-I$(NEWLIB_INCDIR)
PAL_LDFLAGS+=-L$(NEWLIB_LIBDIR)
PAL_LDLIBS+=-lc -lnosys

### regular program rules

CFLAGS=-g -Wall

# Get compile and link flags for app front-end with app-tv back-end
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv
PKG_CFLAGS=$(shell pkg-config --cflags $(PKGCONFIG_DEPS))
PKG_LDLIBS=$(shell pkg-config --libs --static $(PKGCONFIG_DEPS))

# incorporate pkg-config variables
CFLAGS+=$(PKG_CFLAGS)
LDLIBS+=$(PKG_LDLIBS)

OBJS = hello.o
hello: $(OBJS)

# to link against a pal, add depenedencies for the object and linker
# script, and add the linker script to the target's LDFLAGS
hello : $(PAL_NAME).pal.o $(PAL_NAME).pal.ld
hello : LDFLAGS+=-T$(PAL_NAME).pal.ld

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D
