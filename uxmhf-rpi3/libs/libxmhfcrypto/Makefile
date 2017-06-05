srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir) $(srcdir)/hashes/sha1
vpath %.c $(srcdir) $(srcdir)/ciphers/aes

#include $(srcdir)/../../../common.mk

C_SOURCES := hashes/sha1/sha1.c
C_SOURCES += ciphers/aes/aes.c

O_SOURCES := $(C_SOURCES)
O_SOURCES := $(patsubst hashes/sha1/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst ciphers/aes/%, %, $(O_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(O_SOURCES))

LIBXMHFCRYPTO_OBJECTS_DIR = _objs_libxmhfcrypto
THE_ARCHIVE = libxmhfcrypto.a

# targets
.PHONY: verify
verify:
	frama-c -main sha1 -lib-entry -wp -wp-model +cint -wp-prover alt-ergo,cvc3,z3 -cpp-extra-args=-nostdinc $(VFLAGS) $(srcdir)/hashes/sha1/sha1.c


.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFCRYPTO_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	$(CP) $(LIBXMHFCRYPTO_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBXMHFCRYPTO_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(LIBXMHFCRYPTO_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFCRYPTO_OBJECTS_DIR)


