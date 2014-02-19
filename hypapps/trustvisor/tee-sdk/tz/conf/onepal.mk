######### generic rules for a program that uses one pal
# must define: PAL_NAME, PAL_OBJS, PROG_NAME, PROG_OBJS
#
# may also define PKGCONFIG_DEPS, PAL_PKGCONFIG_DEPS, CFLAGS,
# PAL_CFLAGS, etc.

# grab pkgconfig_deps-related flags
CFLAGS+=$(call pkgconfig_cflags, $(PKGCONFIG_DEPS))
LDLIBS+=$(call pkgconfig_ldlibs, $(PKGCONFIG_DEPS))
LDFLAGS+=$(call pkgconfig_ldflags, $(PKGCONFIG_DEPS))

# PAL target
$(PAL_NAME).pal.o : $(PAL_OBJS)

# to link against a pal, add depenedencies for the object and linker
# script, and add the linker script to the target's LDLIBS.
$(PROG_NAME) : $(PAL_NAME).pal.o $(PAL_NAME).pal.ld
$(PROG_NAME) : LDLIBS+=-T$(PAL_NAME).pal.ld

# save objects to be used in recipe, below.
# need this to support multiple inclusion of this file,
# since PROG_OBJS may change, and variables in the recipe are
# evaluated at execution time, not when make reads them
$(PROG_NAME) : OBJS:=$(PROG_OBJS) # need this to support multiple inclusion

# need to explicitly give recipe to prevent make's default recipe from
# adding the pal linker script and object dependencies to the cmd line.
# The pal's palname.pal.o must *NOT* appear explicitly on the linker cmd line,
# since the linker script already pulls it in. Multiple inclusion will result
# in link failure or subtle errors later.
$(PROG_NAME) : $(PROG_OBJS)
	$(CC) $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS)
