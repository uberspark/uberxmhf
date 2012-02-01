C_SOURCES = $(wildcard *.c)

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard ./include/*.h)

CFLAGS += -I./include -nostdinc -fno-builtin -nostdlib -Wall -Werror

THE_ARCHIVE = libemhfc.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c $(C_SOURCES) $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) $(OBJECTS) $(THE_ARCHIVE)

.PHONY: install-dev
install-dev:
	# Nothing to do here
