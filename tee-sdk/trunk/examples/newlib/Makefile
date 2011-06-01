# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

PROG_NAME=hello
PROG_OBJS=hello.o

# Get compile and link flags for app front-end with app-tv back-end
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv
CFLAGS+=$(call pkgconfig_cflags, $(PKGCONFIG_DEPS))
LDLIBS+=$(call pkgconfig_ldlibs, $(PKGCONFIG_DEPS))
LDFLAGS+=$(call pkgconfig_ldflags, $(PKGCONFIG_DEPS))
CFLAGS+=-g -Wall

PAL_NAME=hellopal
PAL_OBJS=hellopal.o pal-aux.o

# extra flags for PAL
PAL_CFLAGS+=-g -Wall

# link pal against newlib
###### newlib paths. should make a pkg-config for this
NEWLIB=../../ports/newlib/install/i586
NEWLIB_LIBDIR=$(NEWLIB)/lib
NEWLIB_INCDIR=$(NEWLIB)/include
######
PAL_CFLAGS+=-I$(NEWLIB_INCDIR)
PAL_LDFLAGS+=-L$(NEWLIB_LIBDIR)
PAL_LDLIBS+=-lc -lnosys

all: $(PROG_NAME)
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS)
.PHONY: clean all

################## generic pal-building rules
PAL_LDFLAGS+=-nostdlib -d -r
PAL_PKGCONFIG_DEPS=tee-sdk-svc tee-sdk-svc-tv
PAL_CFLAGS+=$(call pkgconfig_cflags, $(PAL_PKGCONFIG_DEPS))
# XXX temporarily manually filtering out the old linker script here
PAL_LDFLAGS+=$(filter-out -T%, \
	$(call pkgconfig_ldflags, $(PAL_PKGCONFIG_DEPS)))
PAL_LDLIBS+=$(call pkgconfig_ldlibs, $(PAL_PKGCONFIG_DEPS))
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

######### generic rules for a program that uses one pal
# "inputs": PAL_NAME, PAL_OBJS, PROG_NAME, PROG_OBJS

# PAL target
$(PAL_NAME).pal.o : $(PAL_OBJS)

# to link against a pal, add depenedencies for the object and linker
# script, and add the linker script to the target's LDFLAGS.
$(PROG_NAME) : $(PAL_NAME).pal.ld $(PAL_NAME).pal.o
$(PROG_NAME) : LDLIBS+=-T$(PAL_NAME).pal.ld

# need to explicitly give recipe to prevent make's default recipe from
# adding the pal linker script and object dependencies to the cmd line.
# The pal's palname.pal.o must *NOT* appear explicitly on the linker cmd line,
# since the linker script already pulls it in. Multiple inclusion will result
# in link failure or subtle errors later.
$(PROG_NAME) : $(PROG_OBJS)
	$(CC) $(LDFLAGS) -o $@ $(PROG_OBJS) $(LDLIBS)
#########

#### generic pkgconfig helpers
# to be used with $(call pkgconfig_*, $pkgconfig_dependencies)
pkgconfig_cflags = $(shell pkg-config --cflags $(1))
pkgconfig_ldlibs = $(shell pkg-config --libs-only-l --static $(1))
pkgconfig_ldflags =$(filter-out -l%, $(shell pkg-config --libs --static $(1)))
####

