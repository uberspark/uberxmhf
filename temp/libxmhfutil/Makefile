srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/../libemhfc/include -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall 

LIBXMHFUTIL_OBJECTS_DIR = _objs_libxmhfutil
THE_ARCHIVE = libxmhfutil.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFUTIL_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c 
	#mkdir -p "$(@D)"
	mkdir -p $(LIBXMHFUTIL_OBJECTS_DIR)
	@echo Building "$@" from "$<" 
	$(CC) -c $(CFLAGS) -o $(LIBXMHFUTIL_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFUTIL_OBJECTS_DIR)
	
