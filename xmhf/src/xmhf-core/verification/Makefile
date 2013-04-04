# makefile for XMHF core verification
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  

C_SOURCES = `find ../components/xmhf-sl/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-baseplatform/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-debug/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-dmaprot/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-memprot/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-parteventhub/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-partition/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-runtime/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-smpguest/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-tpm/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-xcphandler/ -type f -name "*.c" -print`
C_SOURCES += `find ../components/xmhf-xmhfcbackend/ -type f -name "*.c" -print`

HYPAPP_SOURCES = `find $(APP_ROOT)/ -type f -name "*.c" -print`

.PHONY: verify 
verify: 
	./check-mprot.sh
	cbmc $(VFLAGS) -D__XMHF_VERIFICATION__ --bounds-check --pointer-check xmhf-core-verify-sl.c  $(HYPAPP_SOURCES) $(C_SOURCES)
	# cbmc $(VFLAGS) -D__XMHF_VERIFICATION__ --bounds-check --pointer-check xmhf-core-vdriver.c  $(HYPAPP_SOURCES) $(C_SOURCES)
	# cbmc $(VFLAGS) -D__XMHF_VERIFICATION__ --bounds-check --pointer-check xmhf-core-vdriver-atomb.c  $(HYPAPP_SOURCES) $(C_SOURCES)
  

  
