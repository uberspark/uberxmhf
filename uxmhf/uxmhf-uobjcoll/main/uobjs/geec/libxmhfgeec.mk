######
# libxmhfgeec Makefile
# author: amit vasudevan (amitvasudevan@acm.org)
######

###### archive name
ARCHIVE = libxmhfgeec.a

###### compute source directory where this Makefile resides
srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)


###### populate sources and objects
C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
CS_SOURCES:= $(wildcard $(srcdir)/*.cS)
CS_SOURCES:= $(patsubst $(srcdir)/%, %, $(CS_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS += $(patsubst %.cS, %.o, $(CS_SOURCES))
CS_CINTERMEDIATE_SOURCES := $(patsubst %.cS, %.o.c, $(CS_SOURCES))
CS_ASMINTERMEDIATE_SOURCES := $(patsubst %.cS, %.o.S, $(CS_SOURCES))
CS_MACHINTERMEDIATE_SOURCES := $(patsubst %.cS, %.o.mach, $(CS_SOURCES))
LIBXMHFGEEC_VERIF_DIR = _verif_libxmhfgeec

###### targets
.PHONY: verify
verify:
	$(MKDIR) -p $(LIBXMHFGEEC_VERIF_DIR)
	$(CP) -f $(srcdir)/xmhfgeec_slabstubs_vft.cS $(LIBXMHFGEEC_VERIF_DIR)/xmhfgeec_slabstubs_vft.cS.c
	$(CP) -f $(srcdir)/xmhfgeec_slabmapdef.c $(LIBXMHFGEEC_VERIF_DIR)/xmhfgeec_slabmapdef.c
	cd $(LIBXMHFGEEC_VERIF_DIR) && $(FRAMAC) -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_FROM_VfT_PROG__ $(V_FLAGS) ../verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(USPARK_INSTALL_HWMDIR)/*.c
	cd $(LIBXMHFGEEC_VERIF_DIR) && $(FRAMAC) -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_uVT_uVU_PROG_TO_VfT_PROG__ $(V_FLAGS) ../verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(USPARK_INSTALL_HWMDIR)/*.c
	cd $(LIBXMHFGEEC_VERIF_DIR) && $(FRAMAC) -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_EXCEPTION__ $(V_FLAGS) ../verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(USPARK_INSTALL_HWMDIR)/*.c
	cd $(LIBXMHFGEEC_VERIF_DIR) && $(FRAMAC) -no-frama-c-stdlib -val -cpp-extra-args=-nostdinc -cpp-extra-args=-D__CALL_INTERCEPT__ $(V_FLAGS) ../verify/xmhfgeec_slabstubs_vft_driver.c xmhfgeec_slabstubs_vft.cS.c xmhfgeec_slabmapdef.c $(USPARK_INSTALL_HWMDIR)/*.c


.PHONY: build
build: $(ARCHIVE)

$(ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(ARCHIVE) $(OBJECTS)

%.o: %.c
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_CFLAGS) -o $@ $<

%.o: %.cS
	@echo Building "$@" from "$<"
	$(CP) -f $< $(@F).c
	$(CCERT) -c -dmach $(CCERT_CASMFLAGS) $(@F).c
	$(FRAMAC) -load-module $(USPARK_INSTALL_TOOLSDIR)/Ucasm -ucasm-infile $(@F).mach -ucasm-outfile $(@F).S
	$(CC) -c $(ASMFLAGS) -o $@ $(@F).S



.PHONY: clean
clean:
	$(RM) $(OBJECTS)
	$(RM) $(CS_CINTERMEDIATE_SOURCES)
	$(RM) $(CS_ASMINTERMEDIATE_SOURCES)
	$(RM) $(CS_MACHINTERMEDIATE_SOURCES)
	$(RM) $(ARCHIVE)
	@for i in $(CS_SOURCES); \
	do \
		($(RM) $$i.c) || exit 1; \
	done;


