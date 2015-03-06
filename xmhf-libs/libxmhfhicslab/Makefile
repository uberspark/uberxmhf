srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.cS $(srcdir)


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
	#$(CC) -c $(CFLAGS) -o $(LIBXMHFHICSLAB_OBJECTS_DIR)/$@ $<
	$(CC) -fomit-frame-pointer -O2 -S -emit-llvm $(CFLAGS) $< -o $(LIBXMHFHICSLAB_OBJECTS_DIR)/$(@F).ll
	cd $(LIBXMHFHICSLAB_OBJECTS_DIR) && fixnaked.pl $(@F).ll
	#cd $(LIBXMHFHICSLAB_OBJECTS_DIR) && llc -O=2 -march=x86-64 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(LIBXMHFHICSLAB_OBJECTS_DIR) && llc -O=2 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	cd $(LIBXMHFHICSLAB_OBJECTS_DIR) && $(CC) -O2 -c $(CFLAGS) $(@F).s -o $(@F)



.PHONY: clean
clean:
	$(RM) -rf $(LIBXMHFHICSLAB_OBJECTS_DIR)

