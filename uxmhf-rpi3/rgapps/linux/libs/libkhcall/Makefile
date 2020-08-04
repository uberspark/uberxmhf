# libkhcall top-level Makefile
# author: amit vasudevan (amitvasudevan@acm.org),
#         matt mccormack (matthew.mccormack@live.com)

srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES := $(wildcard $(srcdir)/*.c)
C_SOURCES := $(patsubst $(srcdir)/%, %, $(C_SOURCES))

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

LIBKHCALL_OBJECTS_DIR = _objs_libkhcall
THE_ARCHIVE = libkhcall.a

# targets
.PHONY: verify
verify:

.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	cd $(LIBKHCALL_OBJECTS_DIR) && $(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)
	$(CP) $(LIBKHCALL_OBJECTS_DIR)/$(THE_ARCHIVE) .

%.o: %.c
	mkdir -p $(LIBKHCALL_OBJECTS_DIR)
	@echo Building "$@" from "$<"
	$(CCERT) -c $(CCERT_FLAGS) -o $(LIBKHCALL_OBJECTS_DIR)/$@ $<


.PHONY: clean
clean:
	$(RM) -rf $(LIBKHCALL_OBJECTS_DIR)
	$(RM) -f ./$(THE_ARCHIVE)

