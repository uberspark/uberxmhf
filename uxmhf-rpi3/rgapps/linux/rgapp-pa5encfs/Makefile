# File: Makefile
# By: Andy Sayler <www.andysayler.com>
# Adopted from work by: Chris Wailes <chris.wailes@gmail.com>
# Project: CSCI 3753 Programming Assignment 5
# Creation Date: 2010/04/06
# Modififed Date: 2012/04/12
# Description:
#	This is the Makefile for PA5.


CC = gcc

CFLAGSFUSE = -D_FILE_OFFSET_BITS=64 -I/usr/include/fuse
LLIBSFUSE = -pthread -lfuse
LLIBSOPENSSL = -lcrypto

CFLAGS = -c -g -Wall
LFLAGS = -g -Wall -Wextra

FUSE_EXAMPLES = example/fusehello example/fusexmp pa5-encfs
XATTR_EXAMPLES = example/xattr-util
OPENSSL_EXAMPLES = example/aes-crypt-util

.PHONY: all fuse-examples xattr-examples openssl-examples clean

all: fuse-examples xattr-examples openssl-examples

fuse-examples: $(FUSE_EXAMPLES)
xattr-examples: $(XATTR_EXAMPLES)
openssl-examples: $(OPENSSL_EXAMPLES)

example/fusehello: example/fusehello.o
	$(CC) $(LFLAGS) $^ -o $@ $(LLIBSFUSE)

example/fusexmp: example/fusexmp.o
	$(CC) $(LFLAGS) $^ -o $@ $(LLIBSFUSE)

pa5-encfs: pa5-encfs.o lib/aes-crypt.o
	$(CC) $(LFLAGS) $^ -o $@ $(LLIBSFUSE) $(LLIBSOPENSSL)

example/xattr-util: example/xattr-util.o
	$(CC) $(LFLAGS) $^ -o $@

example/aes-crypt-util: example/aes-crypt-util.o lib/aes-crypt.o
	$(CC) $(LFLAGS) $^ -o $@ $(LLIBSOPENSSL)

example/fusehello.o: example/fusehello.c
	$(CC) $(CFLAGS) $(CFLAGSFUSE) -o $@ $<

example/fusexmp.o: example/fusexmp.c
	$(CC) $(CFLAGS) $(CFLAGSFUSE) -o $@ $<

pa5-encfs.o: pa5-encfs.c
	$(CC) $(CFLAGS) $(CFLAGSFUSE) $<

example/xattr-util.o: example/xattr-util.c
	$(CC) $(CFLAGS) -o $@ $<

example/aes-crypt-util.o: example/aes-crypt-util.c lib/aes-crypt.h
	$(CC) $(CFLAGS) -o $@ $<

lib/aes-crypt.o: lib/aes-crypt.c lib/aes-crypt.h
	$(CC) $(CFLAGS) -o $@ $<

unmount:
	fusermount -u mir

debug: clean pa5-encfs
	./pa5-encfs -d mnt/ mir/ -e password

mount: clean pa5-encfs
	./pa5-encfs mnt/ mir/ -e password

clean:
	rm -f $(FUSE_EXAMPLES)
	rm -f $(XATTR_EXAMPLES)
	rm -f $(OPENSSL_EXAMPLES)
	rm -f pa5-encfs
	rm -f *.o
	rm -f *~
	rm -f handout/*~
	rm -f handout/*.log
	rm -f handout/*.aux
	rm -f handout/*.out
