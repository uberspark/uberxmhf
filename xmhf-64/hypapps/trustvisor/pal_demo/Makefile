# Compile: make
# Cross compile on x64 Debian: CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld make

CFLAGS := -g -I../src/include -Wall -Werror

BINS = main test test_args
PAL_OBJS = pal.o caller.o

ifeq ($(WINDOWS), y)
	CFLAGS += -DWINDOWS
endif

ifeq ($(CC), x86_64-w64-mingw32-gcc)
PAL_OBJS += translate.o
CFLAGS += -DTRANSLATE
endif

all: $(BINS)

main: main.o $(PAL_OBJS)
test_args: test_args.o $(PAL_OBJS)
test: test.c

pal.o: pal.c
	$(CC) $(CFLAGS) -fno-pic -c -o $@ $^

.PHONY: clean
clean:
	rm -rf *.o $(patsubst %,%.exe,$(BINS)) $(BINS)

