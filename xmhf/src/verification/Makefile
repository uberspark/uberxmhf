# makefile for XMHF core verification
# author: amit vasudevan (amitvasudevan@acm.org)

# get the "source" directory of this Makefile (useful for
# out-of-tree build)
srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

.PHONY: verify
verify:
	mkdir -p $(XMHF_OBJDIR)
	@echo --------------------------------------------------------------
	@echo preparing libxmhfdebug...
	cd $(XMHF_OBJDIR) && $(MAKE) -f $(LIBXMHFDEBUG_SRC)/Makefile -w verify
	@echo libxmhfdebug prepared
	@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo preparing libxmhfhw...
	cd $(XMHF_OBJDIR) && $(MAKE) -f $(LIBXMHFHW_SRC)/Makefile -w verify
	@echo libxmhfhw prepared
	@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo preparing xmhf-secureloader...
	cd $(XMHF_OBJDIR) && $(MAKE) -f $(XMHF_SECURELOADER_SRC)/Makefile -w verify
	@echo xmhf-secureloader prepared
	@echo --------------------------------------------------------------
	@echo --------------------------------------------------------------
	@echo preparing xmhf-runtime...
	cd $(XMHF_OBJDIR) && $(MAKE) -f $(XMHF_RUNTIME_SRC)/Makefile -w verify
	@echo xmhf-runtime prepared
	@echo --------------------------------------------------------------
	#cbmc --ILP32 --little-endian --i386-linux -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ $(VFLAGS) $(srcdir)/verification/xmhf-core-verify-sl.c $(XMHFCORE_OBJECTS_DIR)/_objs_libbaremetal-xmhfbackends/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_libxmhfhw/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-secureloader/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-secureloader/_objs_libxmhfslarch/*.v.c
	#cbmc --ILP32 --little-endian --i386-linux -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ $(VFLAGS) $(srcdir)/verification/xmhf-core-verify-startup.c $(XMHFCORE_OBJECTS_DIR)/_objs_libbaremetal-xmhfbackends/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_libxmhfhw/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/*.v.c $(XMHFCORE_OBJECTS_DIR)/_objs_xmhf-runtime/_objs_libxmhfruntimearch/*.v.c
	cbmc --ILP32 --little-endian --i386-linux -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ $(VFLAGS) $(srcdir)/xmhf-core-verify-eventhub.c $(XMHF_OBJDIR)/_objs_libxmhfdebug/*.v.c $(XMHF_OBJDIR)/_objs_libxmhfhw/*.v.c $(XMHF_OBJDIR)/_objs_xmhf-runtime/*.v.c $(XMHF_OBJDIR)/_objs_xmhf-runtime/_objs_libxmhfruntimearch/*.v.c


# source files
#AS_SOURCES =  

#C_SOURCES = `find ../xmhf-secureloader/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-baseplatform/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-debug/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-dmaprot/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-memprot/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-eventhub/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-partition/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-startup/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-smpguest/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-tpm/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-xcphandler/ -type f -name "*.c" -print`
#C_SOURCES += `find ../xmhf-runtime/xmhf-xmhfcbackend/ -type f -name "*.c" -print`

#HYPAPP_SOURCES = `find $(APP_ROOT)/ -type f -name "*.c" -print`

#.PHONY: verify 
#verify: 
#	cbmc --32 --ILP32 --little-endian --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ --bounds-check --pointer-check xmhf-core-verify-eventhub.c  $(HYPAPP_SOURCES) $(C_SOURCES)
#  
#.PHONY: verifyinit 
#verifyinit: 
#	cbmc --32 --ILP32 --little-endian --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ --bounds-check --pointer-check xmhf-core-verify-sl.c  $(HYPAPP_SOURCES) $(C_SOURCES)
#	cbmc --32 --ILP32 --little-endian --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ --bounds-check --pointer-check xmhf-core-verify-startup.c  $(HYPAPP_SOURCES) $(C_SOURCES)
#
#.PHONY: verifyall 
#verifyall: verifyinit verify
#	./check-mprot.sh
#
#.PHONY: verifysafeupd
#verifysafeupd:
#	cd safeupd && $(MAKE) -w all
