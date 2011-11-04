#-------------------------------------------------------------------------------
# app top-level makefile for apps based on emhf
# author: Zongwei Zhou (zongweiz@andrew.cmu.edu) 

# app-specific configuration options
#

# TODO: Control via configuration
THE_ARCHIVE = ../app_trustvisor.a

# source files
AS_SOURCES = 
C_SOURCES = appmain.c scode.c malloc.c \
		tlsf.c pt.c hc_utpm.c aes.c \
		rsa.c bignum.c random.c linuxrelc.c \
		pages.c \
		dump.c \
		crypto_init.c nv.c


OBJECTS = $(patsubst %.S, $(APPOBJECTSDIR)/%.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, $(APPOBJECTSDIR)/%.o, $(C_SOURCES))

I_SOURCES  =  $(wildcard $(EMHF_INCLUDEDIR)/*.h)
I_SOURCES  +=  $(wildcard $(APP_INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	mkdir -p $(APPOBJECTSDIR)
	$(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

$(APPBOJECTSDIR)/%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
$(APPOBJECTSDIR)/%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean:
	$(RM) -f $(OBJECTS)
