# Compile: make
# Cross compile on x64 Debian: CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld make

CFLAGS := -g -I../src/include -Wall -Werror

all: main test

main: main.o pal.o
test: test.c

main.o: main.c

pal.o: pal.c
	$(CC) $(CFLAGS) -fno-pic -c -o $@ $^

.PHONY: clean
clean:
	rm -rf *.o main test

