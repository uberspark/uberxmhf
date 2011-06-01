#### generic pkgconfig helpers
# to be used with $(call pkgconfig_*, $pkgconfig_dependencies)
pkgconfig_cflags = $(shell pkg-config --cflags $(1))
pkgconfig_ldlibs = $(shell pkg-config --libs-only-l --static $(1))
pkgconfig_ldflags =$(filter-out -l%, $(shell pkg-config --libs --static $(1)))
####
