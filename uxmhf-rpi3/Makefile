#
# uxmhf-rpi3 top-level Makefile
# 
# author: amit vasudevan (amitvasudevan@acm.org)
#
#


check_defined = \
    $(strip $(foreach 1,$1, \
        $(call __check_defined,$1,$(strip $(value 2)))))
__check_defined = \
    $(if $(value $1),, \
        $(error Error: Set $1$(if $2, ($2))$(if $(value @), \
                to OS kernel image file [required by target `$@'])))


TOOLPREFIX ?= arm-linux-gnueabihf-
CFLAGS = -I./include -I../include -c -Wall -nostdlib -nostartfiles -ffreestanding

export TOOLPREFIX
export CFLAGS


.PHONY: all
all: uxmhf-rpi3.img core bootstrap


.PHONY: checkoskrnlimg
checkoskrnlimg:
	@:$(call check_defined, OSKRNLIMG)


entry.o : entry.s
	$(TOOLPREFIX)gcc $(CFLAGS) entry.s -o entry.o

miniuart.o : miniuart.c
	$(TOOLPREFIX)gcc $(CFLAGS) miniuart.c -o miniuart.o

debug.o : debug.c
	$(TOOLPREFIX)gcc $(CFLAGS) debug.c -o debug.o

atags.o : atags.c
	$(TOOLPREFIX)gcc $(CFLAGS) atags.c -o atags.o

main.o : main.c
	$(TOOLPREFIX)gcc $(CFLAGS) main.c -o main.o

uxmhf-rpi3.img: checkoskrnlimg entry.o miniuart.o debug.o atags.o main.o
	$(eval OSKRNLIMG_SIZE := $(shell stat -L -c %s $(OSKRNLIMG)))
	@echo $(OSKRNLIMG_SIZE)
	$(eval OSKRNLIMG_PADSIZE := $(shell echo "4096 -( $(OSKRNLIMG_SIZE) % 4096)" | bc))
	@echo $(OSKRNLIMG_PADSIZE)
	$(eval OSKRNLIMG_FINALSIZE := $(shell echo "$(OSKRNLIMG_SIZE) + $(OSKRNLIMG_PADSIZE) " | bc))
	@echo $(OSKRNLIMG_FINALSIZE_HEX)
	cp $(OSKRNLIMG) ./oskrnlimg.tmp
	truncate --size=$(OSKRNLIMG_FINALSIZE) ./oskrnlimg.tmp 
	$(TOOLPREFIX)ld entry.o miniuart.o debug.o atags.o main.o -T uxmhf-rpi3.lscript -o uxmhf-rpi3.elf
	#$(TOOLPREFIX)objdump -D uxmhf-rpi3.elf > uxmhf-rpi3.list
	$(TOOLPREFIX)objcopy uxmhf-rpi3.elf -O binary uxmhf-rpi3.bin
	cat ./uxmhf-rpi3.bin ./oskrnlimg.tmp > uxmhf-rpi3.img


.PHONY: core
core:
	cd core && make -w all


.PHONY: bootstrap
bootstrap:
	cd bootstrap && make -w all


.PHONY: clean
clean:
	cd core && make -w clean
	cd bootstrap && make -w clean
	rm -f *.o
	rm -f *.img 
	rm -f *.elf
	rm -f *.tmp
	rm -f *.bin