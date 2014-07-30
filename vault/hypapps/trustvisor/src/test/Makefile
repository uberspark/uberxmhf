# CMOCKDIR:=$(realpath ../../../../tools/cmock)
# UNITYDIR:=$(realpath ../../../../tools/cmock/vendor/unity)
# EMHFROOT:=$(CURDIR)/../../../../emhf/trunk/code

CFLAGS := -I${UNITYDIR}/src -DUNITY_SUPPORT_64 -g
CFLAGS := $(filter-out -nostdinc,${CFLAGS})
CFLAGS += -I$(EMHF_ROOT)/libemhfutil/include
CFLAGS += -I$(EMHF_ROOT)/emhfcore/include

all: do_hpt do_drbg # do_pages do_pt

# FIXME should create separately compiled objects here, instead of in src dir
#unity.o: ${UNITYDIR}/src/unity.c
#pt.o: ../app/pt.c

pt: pt_runner.o pt.o ../app/objects/pt.o ${UNITYDIR}/src/unity.o 

hpt: hpt_runner.o hpt.o ${UNITYDIR}/src/unity.o

drbg: test_drbg_runner.o test_drbg.o ../app/objects/dump.o ${UNITYDIR}/src/unity.o 
	$(CC) -o $@ $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS) $(EMHF_ROOT)/libemhfutil/libemhfutil.a

pages: test_pages_runner.o test_pages.o ../app/pages.o ../app/puttymem.o ../app/tlsf.o $(EMHF_ROOT)/x86/libcommon/mpsup.o ${UNITYDIR}/src/unity.o
	$(CC) -o $@ $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS)

do_%: %
	./$<

%_runner.c: %.c
	ruby ${UNITYDIR}/auto/generate_test_runner.rb $< $@



#-------------------------------------------------------------------------------
# app top-level makefile for apps based on emhf
# author: Zongwei Zhou (zongweiz@andrew.cmu.edu) 

# app-specific configuration options
#

# source files
# AS_SOURCES = 
# C_SOURCES = appmain.c scode.c puttymem.c \
# 			malloc.c pt.c tpm_sw.c aes.c \
# 			rsa.c bignum.c sha1.c random.c linuxrelc.c

# OBJECTS = $(patsubst %.S, $(APPOBJECTSDIR)/%.o, $(AS_SOURCES))
# OBJECTS += $(patsubst %.c, $(APPOBJECTSDIR)/%.o, $(C_SOURCES))

# I_SOURCES  =  $(wildcard $(EMHF_INCLUDEDIR)/*.h)
# I_SOURCES  +=  $(wildcard $(APP_INCLUDEDIR)/*.h)

# # targets
# .PHONY: all
# all: $(OBJECTS)

# $(APPBOJECTSDIR)/%.o: %.S $(I_SOURCES) Makefile ../Makefile
# 	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) *.o
	$(RM) *_runner.c
