CURRENT_DIR := $(realpath $(src))
UXMHFRPI3_DIR := $(CURRENT_DIR)/../../..

UINCS = -I$(CURRENT_DIR)/.
UINCS += -I$(UXMHFRPI3_DIR)/include
UINCS += -I$(UXMHFRPI3_DIR)/rgapps/linux/libs/libuhcall/include

EXTRA_CFLAGS := $(UINCS)

obj-m := hypmtschedulertestkmod.o

hypmtschedulertestkmod-objs := hypmtscheduler_testkmod.o hypmtscheduler_kmodlib.o
