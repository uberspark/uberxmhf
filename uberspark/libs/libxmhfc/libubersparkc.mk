######
# libubersparkc Makefile
# author: amit vasudevan (amitvasudevan@acm.org)
######

###### archive name
ARCHIVE = libubersparkc.a

###### compute source directory where this Makefile resides
srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

###### populate sources and objects
C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

###### targets
.PHONY: verify
verify:
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/memcmp.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/memcpy.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/memset.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/memmove.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/strchr.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/strcmp.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/strlen.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/strncmp.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/strncpy.c
	$(FRAMAC) -wp -wp-rte -wp-prover alt-ergo,z3,cvc3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/strnlen.c

.PHONY: build
build: $(ARCHIVE)

$(ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(ARCHIVE) $(OBJECTS)

%.o: %.c
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_CFLAGS) -o $@ $<


.PHONY: clean
clean:
	$(RM) $(OBJECTS)
	$(RM) $(ARCHIVE)
	


