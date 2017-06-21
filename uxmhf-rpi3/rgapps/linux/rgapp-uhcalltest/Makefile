#top-level Makefile for usr mode application to test hypercall
# author: amit vasudevan (amitvasudevan@acm.org)

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..

INCS = $(UXMHFRPI3_DIR)/include
CFLAGS = -I. -I$(INCS) -g -Wall


.PHONY: all
all: 
	arm-linux-gnueabihf-gcc $(CFLAGS) uhcalltest.c -o uhcalltest

.PHONY: clean
clean:
	rm -f uhcalltest
	rm -f *.o
	