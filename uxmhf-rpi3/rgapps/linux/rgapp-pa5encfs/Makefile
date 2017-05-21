# File: Makefile
# By: Andy Sayler <www.andysayler.com>
# Adopted from work by: Chris Wailes <chris.wailes@gmail.com>
# Project: CSCI 3753 Programming Assignment 5
# Creation Date: 2010/04/06
# Modififed Date: 2012/04/12
# Description:
#	This is the Makefile for PA5.
# Modified for uxmhf by amit vasudevan (amitvasudevan@acm.org)


CC = arm-linux-gnueabihf-gcc 

CFLAGSFUSE = -D_FILE_OFFSET_BITS=64 -I. -I/usr/include/fuse
LLIBSFUSE = -pthread -lfuse
LLIBSOPENSSL = -lcrypto

CFLAGS = -c -g -Wall
LFLAGS = -g -Wall -Wextra

.PHONY: all pa5-encfs clean unmount mount debug
all: pa5-encfs

pa5-encfs: pa5-encfs.o aes-crypt.o
	$(CC) $(LFLAGS) $^ -o $@ $(LLIBSFUSE) $(LLIBSOPENSSL)

aes-crypt.o: aes-crypt.c aes-crypt.h
	$(CC) $(CFLAGS) -o $@ $<

pa5-encfs.o: pa5-encfs.c
	$(CC) $(CFLAGS) $(CFLAGSFUSE) $<

unmount:
	fusermount -u mir

debug: clean pa5-encfs
	./pa5-encfs -d mnt/ mir/ -e password

mount: clean pa5-encfs
	./pa5-encfs mnt/ mir/ -e password

clean:
	rm -f pa5-encfs
	rm -f *.o
