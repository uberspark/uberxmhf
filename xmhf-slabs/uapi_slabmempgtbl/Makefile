########################################################################
#
# Makefile for XMHF GEEC sentinel
# author: amit vasudevan (amitvasudevan@acm.org)
#
########################################################################

export srcdir := $(dir $(lastword $(MAKEFILE_LIST)))

vpath %.c $(srcdir)
vpath %.S $(srcdir)
vpath %.cS $(srcdir)
vpath %.lscript $(srcdir)


########################################################################
# options that each slab will customize

export XMHF_SLAB_NAME := uapi_slabmempgtbl
export XMHF_SLAB_TYPE := tprogslab
export XMHF_SLAB_PRIVILEGED := y
export XMHF_SLAB_SOURCES := $(wildcard $(srcdir)/*.c)
#XMHF_SLAB_SOURCES += $(wildcard $(srcdir)/*.cS)

export XMHF_SLAB_GLOBAL_SYMS := --globalize-symbol _dbuf_devpgtbl --globalize-symbol _dbuf_mempgtbl_pml4t --globalize-symbol _dbuf_mempgtbl_pdpt --globalize-symbol _dbuf_mempgtbl_pdt --globalize-symbol _dbuf_mempgtbl_pt

########################################################################
# generic slab build harness
include $(XMHF_DIR)/xmhfslab.mk
