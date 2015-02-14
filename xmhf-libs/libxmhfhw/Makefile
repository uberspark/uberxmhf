srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFHW_OBJECTS_DIR = _objs_libxmhfhw
THE_ARCHIVE = libxmhfhw.a

# targets
.PHONY: all
#all: $(THE_ARCHIVE)
all:

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFC_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c
	#mkdir -p "$(@D)"
	mkdir -p $(LIBXMHFHW_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CC) -c $(CFLAGS) -o $(LIBXMHFHW_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFHW_OBJECTS_DIR)

