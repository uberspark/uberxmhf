srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

#include $(srcdir)/../../../common.mk

C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

LIBUTPM_OBJECTS_DIR = _objs_libutpm
THE_ARCHIVE = libutpm.a

# targets
.PHONY: verify
verify:

.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBUTPM_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	$(CP) $(LIBUTPM_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBUTPM_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(LIBUTPM_OBJECTS_DIR)/$@ $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBUTPM_OBJECTS_DIR)

