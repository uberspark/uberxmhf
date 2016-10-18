srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)


include $(srcdir)/../../../common.mk


C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

CS_SOURCES:= $(wildcard $(srcdir)/*.cS)
CS_SOURCES:= $(patsubst $(srcdir)/%, %, $(CS_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.cS, %.o, $(CS_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFGEEC_OBJECTS_DIR = _objs_libxmhfgeec
LIBXMHFGEEC_VERIF_DIR = _verif_libxmhfgeec

#THE_ARCHIVE = libxmhfgeec.a

# targets
.PHONY: verify
verify:
	mkdir -p $(LIBXMHFGEEC_VERIF_DIR)
	$(CP) -f $(srcdir)/xmhfgeec_slabstubs_vft.cS $(LIBXMHFGEEC_VERIF_DIR)/xmhfgeec_slabstubs_vft.cS.c
	$(CP) -f $(srcdir)/xmhfgeec_slabmapdef.c $(LIBXMHFGEEC_VERIF_DIR)/xmhfgeec_slabmapdef.c
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_FROM_VfT_PROG__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_uVT_uVU_PROG_TO_VfT_PROG__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_EXCEPTION__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_INTERCEPT__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)

.PHONY: all
#all: $(THE_ARCHIVE)
all: $(OBJECTS)
	mkdir -p $(LIBXMHFGEEC_OBJECTS_DIR)
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabmapdef.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabinfotable.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_vft.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_uvt.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_uvu.o .
	cp $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_uvug.o .


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
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_FLAGS) -O0 $(@F).c
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && frama-c -load-script $(XMHF_DIR)/uberspark/tools/ucasm.ml -ucasm-infile $(@F).mach -ucasm-outfile $(@F).S
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
	$(RM) -rf $(LIBXMHFGEEC_VERIF_DIR)

