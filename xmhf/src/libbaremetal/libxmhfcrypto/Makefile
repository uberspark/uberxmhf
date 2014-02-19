srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir) $(srcdir)/ciphers/aes $(srcdir)/hashes/sha1 $(srcdir)/modes/cbc $(srcdir)/mac/hmac $(srcdir)/pk/rsa $(srcdir)/pk/asn1/der $(srcdir)/pk/pkcs1 $(srcdir)/math

#C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES := ciphers/aes/aes.c ciphers/aes/aes_tab.c hashes/sha1/sha1.c modes/cbc/cbc.c mac/hmac/hmac.c pk/rsa/rsa.c pk/asn1/der/der.c pk/pkcs1/pkcs1.c math/math.c math/mpi.c math/mathhelpers.c helpers.c

O_SOURCES := $(C_SOURCES)
O_SOURCES := $(patsubst ciphers/aes/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst hashes/sha1/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst modes/cbc/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst mac/hmac/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst pk/rsa/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst pk/asn1/der/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst pk/pkcs1/%, %, $(O_SOURCES))
O_SOURCES := $(patsubst math/%, %, $(O_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(O_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/../libemhfc/include -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall 

LIBXMHFCRYPTO_OBJECTS_DIR = _objs_libxmhfcrypto
THE_ARCHIVE = libxmhfcrypto.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)
	
$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFCRYPTO_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c 
	#mkdir -p "$(@D)"
	mkdir -p $(LIBXMHFCRYPTO_OBJECTS_DIR)
	@echo Building "$@" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBXMHFCRYPTO_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFCRYPTO_OBJECTS_DIR)


