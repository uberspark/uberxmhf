CFLAGS := -g -I../src/include
# -fno-pic -fno-pie
# LDFLAGS := -fno-pic -fno-pie
# LDFLAGS := -T pal_demo.lds

all: main

main: main.o pal.o
#	$(LD) -o $@ $^

main.o: main.c
pal.o: pal.c

.PHONY: clean
clean:
	rm -rf *.o main

