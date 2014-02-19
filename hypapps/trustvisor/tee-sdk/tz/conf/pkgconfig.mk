#### generic pkgconfig helpers
# to be used with $(call pkgconfig_*, $pkgconfig_dependencies)
PKG_CONFIG ?= pkg-config
pkgconfig_cflags = $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --cflags $(1))
pkgconfig_ldlibs = $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --libs-only-l --static $(1))
pkgconfig_ldflags =$(filter-out -l%, $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) $(PKG_CONFIG) --libs --static $(1)))
####
