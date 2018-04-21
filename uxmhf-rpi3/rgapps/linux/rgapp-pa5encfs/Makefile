# File: Makefile
# By: Andy Sayler <www.andysayler.com>
# Adopted from work by: Chris Wailes <chris.wailes@gmail.com>
# Project: CSCI 3753 Programming Assignment 5
# Creation Date: 2010/04/06
# Modififed Date: 2012/04/12
# Description:
#	This is the Makefile for PA5.
# Modified for uxmhf by amit vasudevan (amitvasudevan@acm.org)

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..
export RGAPPS_LIB_DIR := $(realpath $(CURRENT_DIR)/../libs)
export SYSROOT_USR_DIR := $(realpath $(HOME)/pi-tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/arm-linux-gnueabihf/sysroot/usr)
export SYSROOT_LIB_DIR := $(realpath $(HOME)/pi-tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/arm-linux-gnueabihf/sysroot/lib)

CC = arm-linux-gnueabihf-gcc 

CFLAGSFUSE = -D_FILE_OFFSET_BITS=64 -I. -I/usr/include/fuse

DIR_LIBFUSE = $(SYSROOT_LIB_DIR)/arm-linux-gnueabihf/libfuse.so.2.9.3 
DIR_LIBCRYPTO = $(SYSROOT_USR_DIR)/lib/arm-linux-gnueabihf/libcrypto.so 
DIR_LIBPTHREAD = $(SYSROOT_USR_DIR)/lib/arm-linux-gnueabihf/libpthread.so 
DIR_LIBDL = $(SYSROOT_LIB_DIR)/arm-linux-gnueabihf/libdl.so.2 
DIR_LIBXMHFCRYPTO = $(UXMHFRPI3_DIR)/libs/libxmhfcrypto/libxmhfcrypto.a


LIBS = $(RGAPPS_LIB_DIR)/libuhcall/libuhcall.a
LIBS += $(DIR_LIBXMHFCRYPTO) $(DIR_LIBFUSE) $(DIR_LIBPTHREAD) $(DIR_LIBCRYPTO)  $(DIR_LIBDL)   




INCS = -I$(UXMHFRPI3_DIR)/include
INCS += -I$(RGAPPS_LIB_DIR)/libuhcall/include
INCS += -I../../../libs/libxmhfcrypto/include

CFLAGS = -I. $(INCS) -c -g -Wall
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
