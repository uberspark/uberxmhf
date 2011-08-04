#### generic pkgconfig helpers
# to be used with $(call pkgconfig_*, $pkgconfig_dependencies)
pkgconfig_cflags = $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) pkg-config --cflags $(1))
pkgconfig_ldlibs = $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) pkg-config --libs-only-l --static $(1))
pkgconfig_ldflags =$(filter-out -l%, $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) pkg-config --libs --static $(1)))
####
