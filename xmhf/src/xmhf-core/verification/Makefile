# makefile for XMHF core verification
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  

C_SOURCES = `find ../xmhf-secureloader/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-baseplatform/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-debug/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-dmaprot/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-memprot/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-eventhub/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-partition/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-startup/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-smpguest/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-tpm/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-xcphandler/ -type f -name "*.c" -print`
C_SOURCES += `find ../xmhf-runtime/xmhf-xmhfcbackend/ -type f -name "*.c" -print`

HYPAPP_SOURCES = `find $(APP_ROOT)/ -type f -name "*.c" -print`

.PHONY: verify 
verify: 
	cbmc --32 --ILP32 --little-endian --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ --bounds-check --pointer-check xmhf-core-verify-eventhub.c  $(HYPAPP_SOURCES) $(C_SOURCES)
  
.PHONY: verifyinit 
verifyinit: 
	cbmc --32 --ILP32 --little-endian --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ --bounds-check --pointer-check xmhf-core-verify-sl.c  $(HYPAPP_SOURCES) $(C_SOURCES)
	cbmc --32 --ILP32 --little-endian --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ -D__XMHF_VERIFICATION_DRIVEASSERTS__ --bounds-check --pointer-check xmhf-core-verify-startup.c  $(HYPAPP_SOURCES) $(C_SOURCES)

.PHONY: verifyall 
verifyall: verifyinit verify
	./check-mprot.sh

.PHONY: verifysafeupd
verifysafeupd:
	cd safeupd && $(MAKE) -w all
