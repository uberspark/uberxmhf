FRAMAC_SHARE :=$(shell frama-c-config -print-share-path)
FRAMAC_LIBDIR :=$(shell frama-c-config -print-libpath)
PLUGIN_NAME = Ubp
PLUGIN_CMO = umfcommon ubp
include $(FRAMAC_SHARE)/Makefile.dynamic