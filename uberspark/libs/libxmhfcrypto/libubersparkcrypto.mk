######
# libubersparkcrypto Makefile
# author: amit vasudevan (amitvasudevan@acm.org)
######

###### archive name
ARCHIVE = libubersparkcrypto.a

###### compute source directory where this Makefile resides
srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir) $(srcdir)/hashes/sha1

###### populate sources and objects
C_SOURCES := hashes/sha1/sha1.c
O_SOURCES := $(C_SOURCES)
O_SOURCES := $(patsubst hashes/sha1/%, %, $(O_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(O_SOURCES))


###### targets
.PHONY: verify
verify:
	$(FRAMAC) -main sha1 -lib-entry -wp -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(V_FLAGS) $(srcdir)/hashes/sha1/sha1.c

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
	


