srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

#include $(srcdir)/../../../common.mk

C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

LIBXMHFC_OBJECTS_DIR = _objs_libxmhfc
THE_ARCHIVE = libxmhfc.a

# targets
.PHONY: verify
verify:
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memcmp.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memcpy.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memset.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/memmove.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/strchr.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/strcmp.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/strlen.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/strncmp.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/strncpy.c
	frama-c -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/strnlen.c

.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFC_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	$(CP) $(LIBXMHFC_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBXMHFC_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(LIBXMHFC_OBJECTS_DIR)/$@ $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFC_OBJECTS_DIR)

