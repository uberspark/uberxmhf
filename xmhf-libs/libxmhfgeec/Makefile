srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)


C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

CS_SOURCES:= $(wildcard $(srcdir)/*.cS)
CS_SOURCES:= $(patsubst $(srcdir)/%, %, $(CS_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.cS, %.o, $(CS_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFGEEC_OBJECTS_DIR = _objs_libxmhfgeec
#THE_ARCHIVE = libxmhfgeec.a

# targets
.PHONY: all
#all: $(THE_ARCHIVE)
all: $(OBJECTS)
	mkdir -p $(LIBXMHFGEEC_OBJECTS_DIR)
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabmapdef.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_tprogslab_stubs.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_tprimeslab_stubs.o .


$(THE_ARCHIVE): $(OBJECTS)
	mkdir -p $(LIBXMHFGEEC_OBJECTS_DIR)
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBXMHFGEEC_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) $< -o $(LIBXMHFGEEC_OBJECTS_DIR)/$@
	#$(CC) -fomit-frame-pointer -O2 -S -emit-llvm $(CFLAGS) $< -o $(LIBXMHFGEEC_OBJECTS_DIR)/$(@F).ll
	#cd $(LIBXMHFGEEC_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	#cd $(LIBXMHFGEEC_OBJECTS_DIR) && llc -O=2 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	#cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(CC) -O2 -c $(CFLAGS) $(@F).s -o $(@F)

%.o: %.cS
	mkdir -p $(LIBXMHFGEEC_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	cp -f $< $(LIBXMHFGEEC_OBJECTS_DIR)/$(@F).c
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_FLAGS) $(@F).c
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && extractasm.pl $(@F).mach > $(@F).S
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && gcc -c $(ASFLAGS) -o $@ $(@F).S
	#cd $(LIBXMHFGEEC_OBJECTS_DIR) && mv $(@F).o $@

#%.o: %.cS
#	mkdir -p $(LIBXMHFGEEC_OBJECTS_DIR)
#	@echo Building "$@" from "$<"
#	cp -f $< $(LIBXMHFGEEC_OBJECTS_DIR)/$(@F).c
#	$(CC) -fomit-frame-pointer -O2 -S -emit-llvm $(CFLAGS) $(LIBXMHFGEEC_OBJECTS_DIR)/$(@F).c -o $(LIBXMHFGEEC_OBJECTS_DIR)/$(@F).ll
#	cd $(LIBXMHFGEEC_OBJECTS_DIR) && fixnaked.pl $(@F).ll
#	cd $(LIBXMHFGEEC_OBJECTS_DIR) && llc -O=2 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
#	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(CC) -O2 -c $(CFLAGS) $(@F).s -o $(@F)



.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFGEEC_OBJECTS_DIR)

