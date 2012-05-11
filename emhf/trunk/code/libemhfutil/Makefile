srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)

C_SOURCES:= $(wildcard $(srcdir)/*.c)
C_SOURCES:= $(patsubst $(srcdir)/%, %, $(C_SOURCES))
OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES :=  $(wildcard $(srcdir)/include/*.h)

CFLAGS += -I$(srcdir)/../libemhfc/include -I$(srcdir)/include -nostdinc -fno-builtin -nostdlib -Wall 

THE_ARCHIVE = libemhfutil.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

#%.o: %.c $(C_SOURCES) $(I_SOURCES) Makefile ../Makefile
#	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) $(OBJECTS) $(THE_ARCHIVE)

.PHONY: install-dev
install-dev:
	# Nothing to do here

