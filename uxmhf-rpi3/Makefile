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
	$(TOOLPREFIX)ld entry.o -T uxmhf-rpi3.lscript -o uxmhf-rpi3.elf
	#$(TOOLPREFIX)objdump -D uxmhf-rpi3.elf > uxmhf-rpi3.list
	$(TOOLPREFIX)objcopy uxmhf-rpi3.elf -O binary uxmhf-rpi3.img

.PHONY: clean
clean:
	rm -f *.o
	rm -f *.img 
	rm -f *.elf
	