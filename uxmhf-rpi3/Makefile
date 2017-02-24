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
CFLAGS = -I./include -I../include -c -Wall -nostdlib -nostartfiles -ffreestanding -mcpu=cortex-a53

export TOOLPREFIX
export CFLAGS


.PHONY: all
all: checkoskrnlimg 
	cd core && make -w all
	$(eval OSKRNLIMG_SIZE := $(shell stat -L -c %s $(OSKRNLIMG)))
	@echo $(OSKRNLIMG_SIZE)
	$(eval OSKRNLIMG_PADSIZE := $(shell echo "4096 -( $(OSKRNLIMG_SIZE) % 4096)" | bc))
	@echo $(OSKRNLIMG_PADSIZE)
	$(eval OSKRNLIMG_FINALSIZE := $(shell echo "$(OSKRNLIMG_SIZE) + $(OSKRNLIMG_PADSIZE) " | bc))
	@echo $(OSKRNLIMG_FINALSIZE_HEX)
	cp $(OSKRNLIMG) ./oskrnlimg.tmp
	truncate --size=$(OSKRNLIMG_FINALSIZE) ./oskrnlimg.tmp 
	cd guestos && make -w all
	cd bootstrap && make -w all
	cat ./bootstrap/bootstrap.bin ./oskrnlimg.tmp ./core/core.bin ./guestos/guestos.bin > uxmhf-rpi3.img


.PHONY: checkoskrnlimg
checkoskrnlimg:
	@:$(call check_defined, OSKRNLIMG)


.PHONY: clean
clean:
	cd core && make -w clean
	cd bootstrap && make -w clean
	cd guestos && make -w clean
	rm -f *.o
	rm -f *.img 
	rm -f *.elf
	rm -f *.tmp
	rm -f *.bin