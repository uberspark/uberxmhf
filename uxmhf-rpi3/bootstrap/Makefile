#
# uxmhf-rpi3 bootstrap Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#


.PHONY: all
all: bootstrap.bin

bsentry.o : bsentry.s
	$(TOOLPREFIX)gcc $(CFLAGS) bsentry.s -o bsentry.o

bsmain.o : bsmain.c
	$(TOOLPREFIX)gcc $(CFLAGS) bsmain.c -o bsmain.o

miniuart.o : ../common/miniuart.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/miniuart.c -o miniuart.o

debug.o : ../common/debug.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/debug.c -o debug.o

arm8-32.o : ../common/arm8-32.s
	$(TOOLPREFIX)gcc $(CFLAGS) -D__ASSEMBLY__ ../common/arm8-32.s -o arm8-32.o


bootstrap.bin: bsentry.o bsmain.o miniuart.o arm8-32.o debug.o
	$(TOOLPREFIX)ld bsentry.o bsmain.o miniuart.o arm8-32.o debug.o -T bootstrap.lscript -o bootstrap.elf
	#$(TOOLPREFIX)objdump -D bootstrap.elf > bootstrap.list
	$(TOOLPREFIX)objcopy bootstrap.elf -O binary bootstrap.bin

.PHONY: clean
clean:
	rm -f *.o
	rm -f *.elf
	rm -f *.bin