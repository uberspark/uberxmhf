######
# Makefile for libxmhfdebug
# author: amit vasudevan (amitvasudevan@acm.org)
######

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

LIBXMHFDEBUG_OBJECTS_DIR = _objs_libxmhfdebug
THE_ARCHIVE = libxmhfdebug.a

## targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBXMHFDEBUG_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	$(CP) $(LIBXMHFDEBUG_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	$(MKDIR) -p $(LIBXMHFDEBUG_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_CFLAGS) -o $(LIBXMHFDEBUG_OBJECTS_DIR)/$@ $<

.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFDEBUG_OBJECTS_DIR)

