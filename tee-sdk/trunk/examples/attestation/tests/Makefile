CMOCKDIR=../../../../../tools/cmock
CMOCKOBJ=$(CMOCKDIR)/src/cmock.o
UNITYDIR=$(CMOCKDIR)/vendor/unity
UNITYOBJ=$(UNITYDIR)/src/unity.o

CFLAGS += -I${UNITYDIR}/src -DUNITY_SUPPORT_64 -g
CFLAGS := $(filter-out -nostdinc,${CFLAGS})

LDFLAGS += -lssl -lcrypto -ljson

all: do_json_memory_leaks

# FIXME should create separately compiled objects here, instead of in src dir
#unity.o: ${UNITYDIR}/src/unity.c
#pt.o: ../app/pt.c

json_memory_leaks: json_memory_leaks_runner.o json_memory_leaks.o ../json.o ${UNITYDIR}/src/unity.o
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
	$(RM) *.o *~
	$(RM) *_runner.c
	$(RM) ../app/*.o
