# generic pal-building rules. depends on pkgconfig.mk

# Link the pal into a relocatable object file rather than a
# stand-alone executable.
PAL_LDFLAGS+=-r

# don't use any standard libraries, which may make system calls or
# otherwise be incompatible with the pal.
PAL_LDFLAGS+=-nostdlib

# force allocation of 'common' symbols. we don't want to share
# common symbols with the regular program.
PAL_LDFLAGS+=-d

# use the tee-sdk service front-end with the trustvisor back-end
PAL_PKGCONFIG_DEPS+=tee-sdk-svc tee-sdk-svc-tv

# get flags and libraries specified by pkgconfig
PAL_CFLAGS+=$(call pkgconfig_cflags, $(PAL_PKGCONFIG_DEPS))
# XXX temporarily manually filtering out the old linker script here
PAL_LDFLAGS+=$(filter-out -T%, \
	$(call pkgconfig_ldflags, $(PAL_PKGCONFIG_DEPS)))
PAL_LDLIBS+=$(call pkgconfig_ldlibs, $(PAL_PKGCONFIG_DEPS))

# .pal is a dummy file to be used as a dependency by the regular
# program.
%.pal : %.pal.o %.pal.ld
	touch $@

# use make's default recipes to build pal object files, but substitute
# in pal-specific flags
%.pal.o : LDLIBS = $(PAL_LDLIBS)
%.pal.o : CFLAGS = $(PAL_CFLAGS)
%.pal.o : LDFLAGS = $(PAL_LDFLAGS)

# generate a pal-specific linker script
%.pal.ld: pal-template.ld
	sed 's/PAL_NAME/$*/g' pal-template.ld > $@

# create the pal object file. all symbols except for the entry-point
# (which is assumed to match the %) are made private so as not to conflict
# with the regular program's symbols (e.g., so the pal and regular program
# can use different versions of libc)
%.pal.o: %.o
	ld $(LDFLAGS) -o $@ $^ $(LDLIBS)
	objcopy -G $* $@
	if test `nm -u $@ | wc -l` -ne 0 ; then echo "undefd symbols in $@:"; nm -u $@; rm $@; false; else true; fi
