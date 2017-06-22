#
# linux guest apps and libraries top-level Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#

export CURRENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
export UXMHFRPI3_DIR := $(realpath $(CURRENT_DIR)/../../)

# tools
export AR=ar
export CP=cp
export CCERT=$(TOOLPREFIX)gcc
export CC=$(TOOLPREFIX)gcc
export CCERT_FLAGS=$(CFLAGS)
export RM=rm


TOOLPREFIX ?= arm-linux-gnueabihf-

INCS = -I.
INCS += -I$(CURRENT_DIR)/libs/libuhcall/include

LIBS = $(CURRENT_DIR)/libs/libuhcall/libuhcall.a

CFLAGS = -I. -I$(INCS) -c -g -Wall
CCERTFLAGS = $(CFLAGS)
LFLAGS = -g -Wall -Wextra     

export TOOLPREFIX
export CFLAGS
export CCERTFLAGS
export LIBS


.PHONY: all
all:  
	cd libs/libuhcall && make -w all

.PHONY: clean
clean:
	cd libs/libuhcall && make -w clean

