# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

include pkgconfig.mk pal.mk

PROG_NAME=hello
PROG_OBJS=hello.o
CFLAGS+=-g -Wall
PKGCONFIG_DEPS=tee-sdk-app tee-sdk-app-tv

PAL_NAME=hellopal
PAL_OBJS=hellopal.o pal-aux.o
PAL_CFLAGS+=-g -Wall

all: $(PROG_NAME)
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* $(PROG_NAME) $(PROG_OBJS)
.PHONY: clean all

# grab pkgconfig_deps-related flags
CFLAGS+=$(call pkgconfig_cflags, $(PKGCONFIG_DEPS))
LDLIBS+=$(call pkgconfig_ldlibs, $(PKGCONFIG_DEPS))
LDFLAGS+=$(call pkgconfig_ldflags, $(PKGCONFIG_DEPS))

# link pal against newlib
###### newlib paths. should make a pkg-config for this
NEWLIB=../../ports/newlib/install/i586
NEWLIB_LIBDIR=$(NEWLIB)/lib
NEWLIB_INCDIR=$(NEWLIB)/include
######
PAL_CFLAGS+=-I$(NEWLIB_INCDIR)
PAL_LDFLAGS+=-L$(NEWLIB_LIBDIR)
PAL_LDLIBS+=-lc -lnosys

######### generic rules for a program that uses one pal
# "inputs": PAL_NAME, PAL_OBJS, PROG_NAME, PROG_OBJS

# PAL target
$(PAL_NAME).pal.o : $(PAL_OBJS)

# to link against a pal, add depenedencies for the object and linker
# script, and add the linker script to the target's LDLIBS.
$(PROG_NAME) : $(PAL_NAME).pal
$(PROG_NAME) : LDLIBS+=-T$(PAL_NAME).pal.ld

# need to explicitly give recipe to prevent make's default recipe from
# adding the pal linker script and object dependencies to the cmd line.
# The pal's palname.pal.o must *NOT* appear explicitly on the linker cmd line,
# since the linker script already pulls it in. Multiple inclusion will result
# in link failure or subtle errors later.
$(PROG_NAME) : $(PROG_OBJS)
	$(CC) $(LDFLAGS) -o $@ $(PROG_OBJS) $(LDLIBS)
#########
