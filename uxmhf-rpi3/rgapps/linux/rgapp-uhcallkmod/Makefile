CURRENT_DIR := $(realpath $(src))
UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..

UINCS = -I$(CURRENT_DIR)/.
UINCS += -I$(UXMHFRPI3_DIR)/uobjcoll/uobjs/main/include
UINCS += -I$(UXMHFRPI3_DIR)/rgapps/linux/libs/libuhcall/include

EXTRA_CFLAGS := $(UINCS)

obj-m := uhcallkmod.o
