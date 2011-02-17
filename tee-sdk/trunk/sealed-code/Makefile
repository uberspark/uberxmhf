LIBSCODE=..

CFLAGS+=-I$(LIBSCODE)/include/
CFLAGS+=-Wall
CFLAGS+=-g

all: secret-fun.bin load-code seal-code

seal-code: sealed-code-pal.o sealed-code-pal-interface.o common.o seal-code.o
	$(CC) -T inject.ld -L $(LIBSCODE)/src -lscode -o $@ sealed-code-pal.o sealed-code-pal-interface.o common.o seal-code.o
# sealed-code-pal.o: sealed-code-pal.c sealed-code-pal.h
# 	gcc -Wall -c -I sealed-code-pal.c

load-code: sealed-code-pal.o sealed-code-pal-interface.o common.o load-code.o
	$(CC) -T inject.ld -L $(LIBSCODE)/src -lscode -o $@ sealed-code-pal.o sealed-code-pal-interface.o common.o load-code.o

secret-fun: secret-fun.c
	$(CC) --static -fPIC -nostdlib -o $@ $? -Wall
secret-fun.bin: secret-fun
	objcopy -O binary -j .text -j .rodata ./secret-fun secret-fun.bin

