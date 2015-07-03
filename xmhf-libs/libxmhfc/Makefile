srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

include $(srcdir)/../../common.mk

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFC_OBJECTS_DIR = _objs_libxmhfc
THE_ARCHIVE = libxmhfc.a

# targets
.PHONY: verify
verify:
	#frama-c -wp -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memcmp.c
	#frama-c -wp -wp-rte -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memcpy.c
	frama-c -wp -wp-rte -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memset.c


.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFC_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	cp $(LIBXMHFC_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBXMHFC_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(LIBXMHFC_OBJECTS_DIR)/$@ $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFC_OBJECTS_DIR)

