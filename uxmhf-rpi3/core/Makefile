#
# uxmhf-rpi3 core Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#

.PHONY: all
all: core.bin


entry.o : entry.s
	$(TOOLPREFIX)gcc $(CFLAGS) entry.s -o entry.o


miniuart.o : ../common/miniuart.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/miniuart.c -o miniuart.o

strlen.o : ../common/strlen.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/strlen.c -o strlen.o

subr_prf.o : ../common/subr_prf.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/subr_prf.c -o subr_prf.o


debug.o : ../common/debug.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/debug.c -o debug.o

atags.o : ../common/atags.c
	$(TOOLPREFIX)gcc $(CFLAGS) ../common/atags.c -o atags.o

arm8-32.o : ../common/arm8-32.s
	$(TOOLPREFIX)gcc $(CFLAGS) -D__ASSEMBLY__ ../common/arm8-32.s -o arm8-32.o


hypvtable.o : hypvtable.s
	$(TOOLPREFIX)gcc $(CFLAGS) hypvtable.s -o hypvtable.o

mmu.o : mmu.c
	$(TOOLPREFIX)gcc $(CFLAGS) mmu.c -o mmu.o


s2pgtbl.o : s2pgtbl.c
	$(TOOLPREFIX)gcc $(CFLAGS) s2pgtbl.c -o s2pgtbl.o

main.o : main.c
	$(TOOLPREFIX)gcc $(CFLAGS) main.c -o main.o

core.bin: entry.o miniuart.o strlen.o subr_prf.o debug.o atags.o arm8-32.o hypvtable.o mmu.o s2pgtbl.o main.o
	$(TOOLPREFIX)ld entry.o miniuart.o strlen.o subr_prf.o debug.o atags.o arm8-32.o hypvtable.o mmu.o s2pgtbl.o main.o -T core.lscript -o core.elf $(CCLIB) 
	#$(TOOLPREFIX)objdump -D core.elf > core.list
	$(TOOLPREFIX)objcopy core.elf -O binary core.bin
	
.PHONY: clean
clean:
	rm -f *.o
	rm -f *.elf
	rm -f *.bin