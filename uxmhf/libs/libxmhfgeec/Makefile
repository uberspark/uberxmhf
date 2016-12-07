######
# Makefile for libxmhfgeec
# author: amit vasudevan (amitvasudevan@acm.org)
######

srcdir := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)


C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

CS_SOURCES:= $(wildcard $(srcdir)/*.cS)
CS_SOURCES:= $(patsubst $(srcdir)/%, %, $(CS_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.cS, %.o, $(CS_SOURCES))

LIBXMHFGEEC_OBJECTS_DIR = _objs_libxmhfgeec
LIBXMHFGEEC_VERIF_DIR = _verif_libxmhfgeec

## targets
.PHONY: verify
verify:
	$(MKDIR) -p $(LIBXMHFGEEC_VERIF_DIR)
	$(CP) -f $(srcdir)/xmhfgeec_slabstubs_vft.cS $(LIBXMHFGEEC_VERIF_DIR)/xmhfgeec_slabstubs_vft.cS.c
	$(CP) -f $(srcdir)/xmhfgeec_slabmapdef.c $(LIBXMHFGEEC_VERIF_DIR)/xmhfgeec_slabmapdef.c
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_FROM_VfT_PROG__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_uVT_uVU_PROG_TO_VfT_PROG__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_EXCEPTION__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)
	cd $(LIBXMHFGEEC_VERIF_DIR) && frama-c -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_INTERCEPT__ $(VFLAGS) $(srcdir)/verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(V_XMHFHWM_MODULES)

.PHONY: all
all: $(OBJECTS)
	$(MKDIR) -p $(LIBXMHFGEEC_OBJECTS_DIR)
	$(CP) $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabmapdef.o .
	$(CP) $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_vft.o .
	$(CP) $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_uvt.o .
	$(CP) $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_uvu.o .
	$(CP) $(LIBXMHFGEEC_OBJECTS_DIR)/xmhfgeec_slabstubs_uvug.o .

%.o: %.c
	$(MKDIR) -p $(LIBXMHFGEEC_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_CFLAGS) $< -o $(LIBXMHFGEEC_OBJECTS_DIR)/$@

%.o: %.cS
	$(MKDIR) -p $(LIBXMHFGEEC_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CP) -f $< $(LIBXMHFGEEC_OBJECTS_DIR)/$(@F).c
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(CCERT) -c -dmach $(CCERT_CASMFLAGS) $(@F).c
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(FRAMAC) -load-module $(USPARK_INSTALL_TOOLSDIR)/Ucasm -ucasm-infile $(@F).mach -ucasm-outfile $(@F).S
	cd $(LIBXMHFGEEC_OBJECTS_DIR) && $(CC) -c $(ASMFLAGS) -o $@ $(@F).S


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFGEEC_OBJECTS_DIR)
	$(RM) -rf $(LIBXMHFGEEC_VERIF_DIR)

