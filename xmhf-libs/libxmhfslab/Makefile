srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall

LIBXMHFSLAB_OBJECTS_DIR = _objs_libxmhfslab
THE_ARCHIVE = libxmhfslab.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)
#all:

$(THE_ARCHIVE): $(OBJECTS)
	mkdir -p $(LIBXMHFSLAB_OBJECTS_DIR)
	cd $(LIBXMHFSLAB_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c
	#mkdir -p "$(@D)"
	mkdir -p $(LIBXMHFSLAB_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CC) -c $(CFLAGS) -o $(LIBXMHFSLAB_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFSLAB_OBJECTS_DIR)

