########################################################################
#
# Makefile for verify hypapp
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export PKG_CONFIG ?= pkg-config
export XMHF_PKG_CONFIG_MODNAME=xmhf
XMHF_DATA_DIR=$(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_datadir)
include $(XMHF_DATA_DIR)/xmhfhypapp.mk

########################################################################
# begin hypapp specific build harness

export XMHF_HYPAPP_NAME=hyperdep

C_SOURCES :=  $(wildcard ./src/*.c)
export XMHF_HYPAPP_OBJS := $(patsubst %.c, %.o, $(C_SOURCES))

.PHONY: xmhfhypappall
xmhfhypappall:
		cd src && $(MAKE) -w all

.PHONY: xmhfhypappclean
xmhfhypappclean:
		cd src && $(MAKE) -w clean

