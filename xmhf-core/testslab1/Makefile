########################################################################
#
# Makefile for XMHF slabs
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export srcdir := $(dir $(lastword $(MAKEFILE_LIST)))
vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.lscript $(srcdir)

#export PKG_CONFIG ?= pkg-config
#export XMHF_PKG_CONFIG_MODNAME=xmhf
#XMHF_DATA_DIR=$(shell $(PKG_CONFIG) $(XMHF_PKG_CONFIG_MODNAME) --variable=xmhf_datadir)


############################################################################################
# options that each slab will customize

export XMHF_SLAB_NAME := testslab1
export XMHF_SLAB_PRIVILEGED := y
export XMHF_SLAB_SOURCES := $(wildcard $(srcdir)/*.c)


include $(XMHF_DIR)/xmhfslab.mk
