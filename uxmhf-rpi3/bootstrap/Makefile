#
# uxmhf-rpi3 bootstrap Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#


.PHONY: all
all: bootstrap.bin

bsentry.o : bsentry.S
	$(TOOLPREFIX)gcc $(CFLAGS) bsentry.S -o bsentry.o

bsmain.o : bsmain.c
	$(TOOLPREFIX)gcc $(CFLAGS) bsmain.c -o bsmain.o

#miniuart.o : ../common/miniuart.c
#	$(TOOLPREFIX)gcc $(CFLAGS) ../common/miniuart.c -o miniuart.o

#mailbox.o : ../common/mailbox.c
#	$(TOOLPREFIX)gcc $(CFLAGS) ../common/mailbox.c -o mailbox.o

#pl011uart.o : ../common/pl011uart.c
#	$(TOOLPREFIX)gcc $(CFLAGS) ../common/pl011uart.c -o pl011uart.o

#debug.o : ../common/debug.c
#	$(TOOLPREFIX)gcc $(CFLAGS) ../common/debug.c -o debug.o

arm8-32.o : ../common/arm8-32.s
	$(TOOLPREFIX)gcc $(CFLAGS) -D__ASSEMBLY__ ../common/arm8-32.s -o arm8-32.o


#bootstrap.bin: bsentry.o bsmain.o miniuart.o mailbox.o pl011uart.o arm8-32.o debug.o
#	$(TOOLPREFIX)ld bsentry.o bsmain.o miniuart.o mailbox.o pl011uart.o arm8-32.o debug.o -T bootstrap.lscript -o bootstrap.elf $(LIBS) $(CCLIB)
#	$(TOOLPREFIX)objcopy bootstrap.elf -O binary bootstrap.bin

bootstrap.bin: bsentry.o bsmain.o arm8-32.o
	$(TOOLPREFIX)ld bsentry.o bsmain.o arm8-32.o -T bootstrap.lscript -o bootstrap.elf $(LIBS) $(CCLIB)
	$(TOOLPREFIX)objcopy bootstrap.elf -O binary bootstrap.bin

.PHONY: clean
clean:
	rm -f *.o
	rm -f *.elf
	rm -f *.bin