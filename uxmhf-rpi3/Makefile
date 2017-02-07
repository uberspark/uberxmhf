#
# uxmhf-rpi3 top-level Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#

TOOLPREFIX ?= arm-linux-gnueabihf-
CFLAGS = -I. -c -Wall -nostdlib -nostartfiles -ffreestanding

.PHONY: all
all: uxmhf-rpi3.img uxmhf-rpi3-bootstrap.img

entry.o : entry.s
	$(TOOLPREFIX)gcc $(CFLAGS) entry.s -o entry.o

miniuart.o : miniuart.c
	$(TOOLPREFIX)gcc $(CFLAGS) miniuart.c -o miniuart.o

atags.o : atags.c
	$(TOOLPREFIX)gcc $(CFLAGS) atags.c -o atags.o

main.o : main.c
	$(TOOLPREFIX)gcc $(CFLAGS) main.c -o main.o

uxmhf-rpi3.img: entry.o miniuart.o atags.o main.o
	$(TOOLPREFIX)ld entry.o miniuart.o atags.o main.o -T uxmhf-rpi3.lscript -o uxmhf-rpi3.elf
	#$(TOOLPREFIX)objdump -D uxmhf-rpi3.elf > uxmhf-rpi3.list
	$(TOOLPREFIX)objcopy uxmhf-rpi3.elf -O binary uxmhf-rpi3.img


bootstrap.o : bootstrap.s
	$(TOOLPREFIX)gcc $(CFLAGS) bootstrap.s -o bootstrap.o

uxmhf-rpi3-bootstrap.img: bootstrap.o
	$(TOOLPREFIX)ld bootstrap.o -T uxmhf-rpi3-bootstrap.lscript -o uxmhf-rpi3-bootstrap.elf
	#$(TOOLPREFIX)objdump -D uxmhf-rpi3-bootstrap.elf > uxmhf-rpi3-bootstrap.list
	$(TOOLPREFIX)objcopy uxmhf-rpi3-bootstrap.elf -O binary uxmhf-rpi3-bootstrap.img


.PHONY: clean
clean:
	rm -f *.o
	rm -f *.img 
	rm -f *.elf
	