# makefile for xmhfcil -- XMHF cil driver
# author: amit vasudevan (amitvasudevan@acm.org)


# source files
OCAML_SOURCES = options.ml cammwrite.ml main.ml 

AS_SOURCES =  

C_SOURCES += `find ../../../xmhf-runtime/xmhf-baseplatform/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-debug/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-dmaprot/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-memprot/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-eventhub/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-partition/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-startup/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-smpguest/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-tpm/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-xcphandler/ -type f -name "*.c" -print`
C_SOURCES += `find ../../../xmhf-runtime/xmhf-xmhfcbackend/ -type f -name "*.c" -print`

HYPAPP_SOURCES = `find $(APP_ROOT)/ -type f -name "*.c" -print`

# corresponding object files
OBJECTS = $(patsubst %.ml, %.cmx, $(OCAML_SOURCES))

# libraries used
OCAML_LIBS = unix,str,cil

export CIL_MACHINE := bool=1,1 short=2,2 int=4,4 long=4,4 long_long=8,4 float=4,4 double=4,4 long_double=12,4 pointer=4,4 enum=4,4 void=1 fun=1,1 alignof_string=1 max_alignment=16 size_t=unsigned_int wchar_t=int char_is_unsigned=false little_endian=true const_string_literals=true big_endian=false __thread_is_keyword=true __builtin_va_list=true underscore_name=false

# targets
.PHONY: all

all: xmhfcil.exe xmhfsafeupd

xmhfcil.exe: $(OBJECTS)
	ocamlfind ocamlopt -package $(OCAML_LIBS) -linkpkg -o xmhfcil.exe $(OBJECTS)

%.cmx: %.ml Makefile
	ocamlfind ocamlopt -c $< -package $(OCAML_LIBS)

.PHONY: clean 
clean: 
	$(RM) -rf *.cmx
	$(RM) -rf xmhfcil.exe
	$(RM) -rf *.cil.c
	$(RM) -rf *.i
	$(RM) -rf *.o
	$(RM) -rf *.cmi
	$(RM) -rf *.out
	
.PHONY: xmhfsafeupd
xmhfsafeupd: xmhfcil.exe
	mkdir -p ./temp-cil
	cd temp-cil && ../xmhfcil --save-temps=. -c $(CFLAGS) -D__XMHF_VERIFICATION__ $(HYPAPP_SOURCES) $(C_SOURCES)
	cd temp-cil && cbmc --ILP32 --32 --i386-linux $(VFLAGS) -D__XMHF_VERIFICATION__ --bounds-check --pointer-check ../../xmhf-core-verify-eventhub.c runtime.cil.c rntm-*.cil.c bplt-*.cil.c dbg-*.cil.c dmap-*.cil.c peh-*.cil.c part-*.cil.c xcph-*.cil.c xmhfc-*.cil.c tpm-*.cil.c smpg-*.cil.c memp-*.cil.c
	
