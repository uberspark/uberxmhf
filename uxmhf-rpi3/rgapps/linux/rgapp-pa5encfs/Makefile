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
DIR_LIBFUSE = /home/amit/work/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/arm-linux-gnueabihf/sysroot/lib/arm-linux-gnueabihf/libfuse.so.2.9.3 
DIR_LIBCRYPTO = /home/amit/work/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/arm-linux-gnueabihf/sysroot/usr/lib/arm-linux-gnueabihf/libcrypto.so 
DIR_LIBPTHREAD = /home/amit/work/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/arm-linux-gnueabihf/sysroot/usr/lib/arm-linux-gnueabihf/libpthread.so 
DIR_LIBDL = /home/amit/work/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/arm-linux-gnueabihf/sysroot/lib/arm-linux-gnueabihf/libdl.so.2 
LIBS = $(DIR_LIBFUSE) $(DIR_LIBPTHREAD) $(DIR_LIBCRYPTO)  $(DIR_LIBDL)   

CFLAGS = -c -g -Wall
LFLAGS = -g -Wall -Wextra     

.PHONY: all pa5-encfs clean unmount mount debug
all: pa5-encfs

pa5-encfs: pa5-encfs.o aes-crypt.o
	$(CC) $(LFLAGS) $^ -o $@ $(LIBS)

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
