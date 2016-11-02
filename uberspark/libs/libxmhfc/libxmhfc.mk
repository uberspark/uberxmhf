######
# libubersparkc Makefile
# author: amit vasudevan (amitvasudevan@acm.org)
######

###### compute source directory where this Makefile resides
srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

###### include common boilerplate Makefile code
include $(srcdir)/../../common.mk

###### populate sources and objects
C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

###### archive name
ARCHIVE = libubersparkc.a

###### targets
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

.PHONY: build
build: $(ARCHIVE)

$(ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(ARCHIVE) $(OBJECTS)

%.o: %.c
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $@ $<


.PHONY: clean
clean:
	$(RM) $(OBJECTS)
	$(RM) $(ARCHIVE)
	


