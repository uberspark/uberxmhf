CURRENT_DIR := $(realpath $(src))
UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..

UINCS = -I$(CURRENT_DIR)/.
UINCS += -I$(UXMHFRPI3_DIR)/uobjcoll/uobjs/main/include
#rgapps/linux/libs/libkhcall/include

UINCS += -I$(UXMHFRPI3_DIR)/rgapps/linux/libs/libkhcall/include
UINCS += -I$(UXMHFRPI3_DIR)/rgapps/linux/libs/libuhcall/include

EXTRA_CFLAGS := $(UINCS)

obj-m := khcallkmod.o
