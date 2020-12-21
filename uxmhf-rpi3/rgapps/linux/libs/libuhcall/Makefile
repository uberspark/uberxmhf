# libuhcall top-level Makefile
# author: amit vasudevan (amitvasudevan@acm.org)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

CFLAGS = -I. -Iinclude -c -g -Wall

LIBUHCALL_OBJECTS_DIR = _objs_libuhcall
THE_ARCHIVE = libuhcall.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBUHCALL_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	cp $(LIBUHCALL_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBUHCALL_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	arm-linux-gnueabihf-gcc $(CFLAGS) -o $(LIBUHCALL_OBJECTS_DIR)/$@ $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBUHCALL_OBJECTS_DIR)
	$(RM) -f ./$(THE_ARCHIVE)

