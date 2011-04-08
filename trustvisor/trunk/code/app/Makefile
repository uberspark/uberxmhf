#-------------------------------------------------------------------------------
# app top-level makefile for apps based on emhf
# author: Zongwei Zhou (zongweiz@andrew.cmu.edu) 

# app-specific configuration options
#

# source files
AS_SOURCES = 
C_SOURCES = appmain.c scode.c puttymem.c \
			tlsf.c pt.c tpm_sw.c aes.c \
			rsa.c bignum.c sha1.c random.c linuxrelc.c

OBJECTS = $(patsubst %.S, $(APPOBJECTSDIR)/%.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, $(APPOBJECTSDIR)/%.o, $(C_SOURCES))

I_SOURCES  =  $(wildcard $(EMHF_INCLUDEDIR)/*.h)
I_SOURCES  +=  $(wildcard $(APP_INCLUDEDIR)/*.h)

# targets
.PHONY: all
all: $(OBJECTS)

$(APPBOJECTSDIR)/%.o: %.S $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(ASFLAGS) -o $@ $<
$(APPOBJECTSDIR)/%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
