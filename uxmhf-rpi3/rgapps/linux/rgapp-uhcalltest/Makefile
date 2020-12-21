#top-level Makefile for usr mode application to test hypercall
# author: amit vasudevan (amitvasudevan@acm.org)

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..
export RGAPPS_LIB_DIR := $(realpath $(CURRENT_DIR)/../libs)

INCS = -I$(UXMHFRPI3_DIR)/include
INCS += -I$(RGAPPS_LIB_DIR)/libuhcall/include

LIBS = $(RGAPPS_LIB_DIR)/libuhcall/libuhcall.a


CFLAGS = -I. $(INCS) -c -g -Wall
LFLAGS = -g -Wall -Wextra     


.PHONY: all
all: 
	cd $(RGAPPS_LIB_DIR)/libuhcall && make -w all
	arm-linux-gnueabihf-gcc $(CFLAGS) uhcalltest.c -o uhcalltest.o
	arm-linux-gnueabihf-gcc $(LFLAGS) uhcalltest.o -o uhcalltest $(LIBS)

.PHONY: clean
clean:
	rm -f uhcalltest
	rm -f *.o
	