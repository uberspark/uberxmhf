#top-level Makefile for usr mode application to test micro-tpm
# author: amit vasudevan (amitvasudevan@acm.org)

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..
export RGAPPS_LIB_DIR := $(realpath $(CURRENT_DIR)/../libs)

INCS = -I$(UXMHFRPI3_DIR)/uobjcoll/main/include
INCS += -I$(RGAPPS_LIB_DIR)/libuhcall/include
INCS += -I$(UXMHFRPI3_DIR)/libs/libxmhfcrypto/include
INCS += -I$(UXMHFRPI3_DIR)/libs/libutpm/include

LIBS = $(RGAPPS_LIB_DIR)/libuhcall/libuhcall.a
LIBS += $(UXMHFRPI3_DIR)/libs/libutpm/libutpm.a
LIBS += $(UXMHFRPI3_DIR)/libs/libxmhfcrypto/libxmhfcrypto.a


CFLAGS = -I. $(INCS) -c -g -Wall
LFLAGS = -g -Wall -Wextra     


.PHONY: all
all: 
	arm-linux-gnueabihf-gcc $(CFLAGS) utpmtest.c -o utpmtest.o
	arm-linux-gnueabihf-gcc $(LFLAGS) utpmtest.o -o utpmtest $(LIBS)

.PHONY: clean
clean:
	rm -f utpmtest
	rm -f *.o
	