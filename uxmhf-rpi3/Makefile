#
# uxmhf-rpi3 top-level Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#

TOOLPREFIX ?= arm-linux-gnueabihf-
CFLAGS = -c -Wall -nostdlib -nostartfiles -ffreestanding

.PHONY: all
all: uxmhf-rpi3.img

entry.o : entry.s
	$(TOOLPREFIX)gcc $(CFLAGS) entry.s -o entry.o

uxmhf-rpi3.img: entry.o

.PHONY: clean
clean:
	rm -f *.o
	rm -f *.img 
	