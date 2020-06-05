#top-level Makefile for usr mode application to test hypercall
# author: amit vasudevan (amitvasudevan@acm.org)

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..
export RGAPPS_LIB_DIR := $(realpath $(CURRENT_DIR)/../libs)

INCS = -I$(UXMHFRPI3_DIR)/include
INCS += -I$(RGAPPS_LIB_DIR)/libuhcall/include
INCS += -I$(UXMHFRPI3_DIR)/libs/libxmhfcrypto/include

LIBS = $(RGAPPS_LIB_DIR)/libuhcall/libuhcall.a
LIBS += $(UXMHFRPI3_DIR)/libs/libxmhfcrypto/libxmhfcrypto.a

CFLAGS = -I. $(INCS) -c -g -Wall
LFLAGS = -g -Wall -Wextra     


.PHONY: all
all: 
	arm-linux-gnueabihf-gcc $(CFLAGS) client.c -o client.o
	arm-linux-gnueabihf-gcc $(CFLAGS) server.c -o server.o
	arm-linux-gnueabihf-gcc $(CFLAGS) demo.c -o demo.o
	arm-linux-gnueabihf-gcc $(LFLAGS) client.o -o client $(LIBS)
	arm-linux-gnueabihf-gcc $(LFLAGS) server.o -o server $(LIBS)
	arm-linux-gnueabihf-gcc $(LFLAGS) demo.o -o demo $(LIBS)

local:
	gcc $(CFLAGS) client.c -o client.o
	gcc $(CFLAGS) server.c -o server.o
	gcc $(CFLAGS) demo.c -o demo.o
	gcc $(LFLAGS) client.o -o client $(LIBS)
	gcc $(LFLAGS) server.o -o server $(LIBS)
	gcc $(LFLAGS) demo.o -o demo $(LIBS)

.PHONY: clean
clean:
	rm -f client server demo
	rm -f *.o
