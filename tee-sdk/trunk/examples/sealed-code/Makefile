LIBSCODE=../../tz/dev/tv

CFLAGS+=-I$(LIBSCODE)/include
CFLAGS+=-L../../tz
CFLAGS+=-Wall
CFLAGS+=-g

all: secret-fun.bin load-code seal-code

seal-code: sealed-code-pal.o sealed-code-pal-interface.o common.o seal-code.o
	$(CC) $(CFLAGS) -T inject.ld -o $@ sealed-code-pal.o sealed-code-pal-interface.o common.o seal-code.o -ltz
# sealed-code-pal.o: sealed-code-pal.c sealed-code-pal.h
# 	gcc -Wall -c -I sealed-code-pal.c

load-code: sealed-code-pal.o sealed-code-pal-interface.o common.o load-code.o
	$(CC) $(CFLAGS) -T inject.ld -o $@ sealed-code-pal.o sealed-code-pal-interface.o common.o load-code.o -ltz

secret-fun: secret-fun.c
	$(CC) --static -fPIC -nostdlib -o $@ $? -Wall
secret-fun.bin: secret-fun
	objcopy -O binary -j .text -j .rodata ./secret-fun secret-fun.bin

