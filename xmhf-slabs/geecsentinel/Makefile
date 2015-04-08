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

export XMHF_SLAB_NAME := geecsentinel
export XMHF_SLAB_PRIVILEGED := y
export XMHF_SLAB_SOURCES := $(wildcard $(srcdir)/*.c)
XMHF_SLAB_SOURCES += $(wildcard $(srcdir)/*.cS)

export XMHF_SLAB_GLOBAL_SYMS := 						\
	--globalize-symbol __xmhfhic_rtm_uapihandler 		\
	--globalize-symbol __xmhfhic_rtm_exception_stub 	\
	--globalize-symbol __xmhfhic_rtm_intercept 			\
	--globalize-symbol __xmhfhic_rtm_trampolinehandler 	\
	--globalize-symbol _xmhfhic_common_slab_info_table 	\
	--globalize-symbol __xmhfhic_rtm_trampoline_stub 	\
	--globalize-symbol __xmhfhic_rtm_intercept_stub		\
	--globalize-symbol __xmhf_exception_handler_0  \
	--globalize-symbol __xmhf_exception_handler_1  \
	--globalize-symbol __xmhf_exception_handler_2  \
	--globalize-symbol __xmhf_exception_handler_3  \
	--globalize-symbol __xmhf_exception_handler_4  \
	--globalize-symbol __xmhf_exception_handler_5  \
	--globalize-symbol __xmhf_exception_handler_6  \
	--globalize-symbol __xmhf_exception_handler_7  \
	--globalize-symbol __xmhf_exception_handler_8  \
	--globalize-symbol __xmhf_exception_handler_9  \
	--globalize-symbol __xmhf_exception_handler_10 \
	--globalize-symbol __xmhf_exception_handler_11 \
	--globalize-symbol __xmhf_exception_handler_12 \
	--globalize-symbol __xmhf_exception_handler_13 \
	--globalize-symbol __xmhf_exception_handler_14 \
	--globalize-symbol __xmhf_exception_handler_15 \
	--globalize-symbol __xmhf_exception_handler_16 \
	--globalize-symbol __xmhf_exception_handler_17 \
	--globalize-symbol __xmhf_exception_handler_18 \
	--globalize-symbol __xmhf_exception_handler_19 \
	--globalize-symbol __xmhf_exception_handler_20 \
	--globalize-symbol __xmhf_exception_handler_21 \
	--globalize-symbol __xmhf_exception_handler_22 \
	--globalize-symbol __xmhf_exception_handler_23 \
	--globalize-symbol __xmhf_exception_handler_24 \
	--globalize-symbol __xmhf_exception_handler_25 \
	--globalize-symbol __xmhf_exception_handler_26 \
	--globalize-symbol __xmhf_exception_handler_27 \
	--globalize-symbol __xmhf_exception_handler_28 \
	--globalize-symbol __xmhf_exception_handler_29 \
	--globalize-symbol __xmhf_exception_handler_30 \
	--globalize-symbol __xmhf_exception_handler_31

########################################################################
# generic slab build harness
include $(XMHF_DIR)/xmhfslab.mk
