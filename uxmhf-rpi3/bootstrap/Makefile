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

bootstrap.bin: bsentry.o
	$(TOOLPREFIX)ld bsentry.o -T bootstrap.lscript -o bootstrap.elf
	#$(TOOLPREFIX)objdump -D bootstrap.elf > bootstrap.list
	$(TOOLPREFIX)objcopy bootstrap.elf -O binary bootstrap.bin

.PHONY: clean
clean:
	rm -f *.o
	rm -f *.elf
	rm -f *.bin