#
# uxmhf-rpi3 core Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#

.PHONY: all
all: guestos.bin


entry.o : entry.s
	$(TOOLPREFIX)gcc $(CFLAGS) entry.s -o entry.o

miniuart.o : ../common/miniuart.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/miniuart.c -o miniuart.o

debug.o : ../common/debug.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/debug.c -o debug.o

main.o : main.c
	$(TOOLPREFIX)gcc $(CFLAGS) main.c -o main.o

guestos.bin: entry.o miniuart.o debug.o main.o
	$(TOOLPREFIX)ld entry.o miniuart.o debug.o main.o -T guestos.lscript -o guestos.elf
	#$(TOOLPREFIX)objdump -D core.elf > core.list
	$(TOOLPREFIX)objcopy guestos.elf -O binary guestos.bin

.PHONY: clean
clean:
	rm -f *.o
	rm -f *.elf
	rm -f *.bin