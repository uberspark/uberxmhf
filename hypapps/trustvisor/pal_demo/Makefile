# Compile: make
# Cross compile on x64 Debian: CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld make

CFLAGS := -g -I../src/include -Wall -Werror

ifeq ($(WINDOWS), y)
	CFLAGS += -DWINDOWS
endif

all: main test test_args

main: main.o pal.o caller.o
test_args: test_args.o pal.o caller.o
test: test.c

pal.o: pal.c
	$(CC) $(CFLAGS) -fno-pic -c -o $@ $^

.PHONY: clean
clean:
	rm -rf *.o *.exe main test test_args

