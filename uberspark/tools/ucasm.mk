FRAMAC_SHARE :=$(shell frama-c-config -print-share-path)
FRAMAC_LIBDIR :=$(shell frama-c-config -print-libpath)
PLUGIN_NAME = Ucasm
PLUGIN_CMO = umfcommon ucasm
include $(FRAMAC_SHARE)/Makefile.dynamic