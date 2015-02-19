srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFHICSLAB_OBJECTS_DIR = _objs_libxmhfhicslab
THE_ARCHIVE = libxmhfhicslab.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)
#all:

$(THE_ARCHIVE): $(OBJECTS)
	mkdir -p $(LIBXMHFHICSLAB_OBJECTS_DIR)
	cd $(LIBXMHFHICSLAB_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c
	#mkdir -p "$(@D)"
	mkdir -p $(LIBXMHFHICSLAB_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CC) -c $(CFLAGS) -o $(LIBXMHFHICSLAB_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFHICSLAB_OBJECTS_DIR)

