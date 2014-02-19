srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/../libemhfc/include -I$(srcdir)/../libemhfcrypto/include -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall 

LIBTV_UTPM_OBJECTS_DIR = _objs_libtv_utpm
THE_ARCHIVE = libtv_utpm.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBTV_UTPM_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c 
	#mkdir -p "$(@D)"
	mkdir -p $(LIBTV_UTPM_OBJECTS_DIR)
	@echo Building "$@" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBTV_UTPM_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBTV_UTPM_OBJECTS_DIR)

