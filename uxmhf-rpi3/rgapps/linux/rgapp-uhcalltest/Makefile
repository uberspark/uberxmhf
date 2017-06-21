#top-level Makefile for usr mode application to test hypercall
# author: amit vasudevan (amitvasudevan@acm.org)

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..

INCS = -I$(UXMHFRPI3_DIR)/include
INCS += -I$(UXMHFRPI3_DIR)/libs/libuhcall/include

CFLAGS = -I. $(INCS) -g -Wall


.PHONY: all
all: 
	arm-linux-gnueabihf-gcc $(CFLAGS) uhcalltest.c -o uhcalltest

.PHONY: clean
clean:
	rm -f uhcalltest
	rm -f *.o
	