########################################################################
#
# Makefile for XMHF GEEC sentinel
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export srcdir := $(dir $(lastword $(MAKEFILE_LIST)))

vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.lscript $(srcdir)


########################################################################
# options that each slab will customize

export XMHF_SLAB_NAME := geecsentinel
export XMHF_SLAB_PRIVILEGED := y
export XMHF_SLAB_SOURCES := $(wildcard $(srcdir)/*.c)


########################################################################
# generic slab build harness
include $(XMHF_DIR)/xmhfslab.mk
