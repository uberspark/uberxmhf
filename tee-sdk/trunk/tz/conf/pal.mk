# generic pal-building rules. depends on pkgconfig.mk

# get flags and libraries specified by pkgconfig
PAL_CFLAGS+=$(call pkgconfig_cflags, $(PAL_PKGCONFIG_DEPS))
PAL_LDFLAGS+=$(call pkgconfig_ldflags, $(PAL_PKGCONFIG_DEPS))
PAL_LDLIBS+=$(call pkgconfig_ldlibs, $(PAL_PKGCONFIG_DEPS))

# use make's default recipes to build pal object files, but substitute
# in pal-specific flags
%.pal.o : LDLIBS = $(PAL_LDLIBS)
%.pal.o : CFLAGS = $(PAL_CFLAGS)
%.pal.o : LDFLAGS = $(PAL_LDFLAGS)

# generate a pal-specific linker script
%.pal.ld :
	sed 's/PAL_NAME/$*/g' $(TEESDK_DATA_DIR)/pal-template.ld > $@

# create the pal object file. all symbols except for the entry-point
# (which is assumed to match the %) are made private so as not to conflict
# with the regular program's symbols (e.g., so the pal and regular program
# can use different versions of libc)
%.pal.o: %.o
	ld $(LDFLAGS) -o $@ $^ $(LDLIBS)
	objcopy -G $* $@
	if test `nm -u $@ | wc -l` -ne 0 ; then echo "undefd symbols in $@:"; nm -u $@; rm $@; false; else true; fi
