srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/../libxmhfc/include -I$(srcdir)/../libxmhfcrypto/include -I$(srcdir)/../libxmhfutil/include -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall 

LIBTPM_OBJECTS_DIR = _objs_libtpm
THE_ARCHIVE = libtpm.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBTPM_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c 
	#mkdir -p "$(@D)"
	mkdir -p $(LIBTPM_OBJECTS_DIR)
	@echo Building "$@" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBTPM_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBTPM_OBJECTS_DIR)

