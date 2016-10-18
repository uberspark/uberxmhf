FRAMAC_SHARE :=$(shell frama-c-config -print-share-path)
FRAMAC_LIBDIR :=$(shell frama-c-config -print-libpath)
PLUGIN_NAME = Umf
PLUGIN_CMO = umfcommon umfmain
include $(FRAMAC_SHARE)/Makefile.dynamic