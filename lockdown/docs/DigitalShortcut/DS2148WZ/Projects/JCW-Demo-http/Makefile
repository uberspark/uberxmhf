#
#  $Id: Makefile 68 2008-10-05 22:15:33Z jcw $
#  $Revision: 68 $
#  $Author: jcw $
#  $Date: 2008-10-05 18:15:33 -0400 (Sun, 05 Oct 2008) $
#  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/Makefile $
#

.SILENT: 
.DELETE_ON_ERROR:

#
#  -D CFG_CONSOLE_USB   for console on USB
#  -D CFG_CONSOLE_UART0 for console on UART0
#  -D CFG_CONSOLE_UART1 for console on UART1 instead of USB (disables GPS task, baud rate set to 115200)
#  -D CFG_USB_MSC       to use SD/MMC as a mass storage class device over USB
#

#export LPC2148DEMO_OPTS=-D CFG_CONSOLE_USB
export LPC2148DEMO_OPTS=-D CFG_CONSOLE_UART0
#
#  These shouldn't need to be changed
#
export CC=arm-elf-gcc
export AR=arm-elf-ar
export OBJCOPY=arm-elf-objcopy
export OBJDUMP=arm-elf-objdump
export CRT0=boot.s
export WARNINGS=-Wall -Wextra -Wshadow -Wpointer-arith -Wbad-function-cast -Wcast-align -Wsign-compare -Waggregate-return -Wstrict-prototypes -Wmissing-prototypes -Wmissing-declarations -Wunused
export CFLAGS=$(WARNINGS) -D RUN_MODE=RUN_FROM_ROM -D GCC_ARM7 $(INCLUDES) $(BASEINCLUDE) -mcpu=arm7tdmi -T$(LDSCRIPT) -g -O3 -fomit-frame-pointer $(LPC2148DEMO_OPTS)
export LDSCRIPT=lpc2148-rom.ld
export LINKER_FLAGS=$(COMMON)/common.a -Xlinker -oJWDemoHttp.elf -Xlinker -M -Xlinker -Map=JWDemoHttp.map
export ROOT=$(shell pwd)
export BASEINCLUDE=-I$(ROOT) -I$(ROOT)/FreeRTOS/include
export COMMON=$(ROOT)/common

#
#  Project sub-directories
#
SUBDIRS=FreeRTOS cpu digi_short eints fatfs fiq i2c leds mmc monitor newlib swi timer uart usb usbser wiz5300

SRC_FILES = main.c

ARM_OBJ = $(SRC_FILES:.c=.o)

.PHONY: all
all : subdirs JWDemoHttp.hex

.PHONY: subdirs $(SUBDIRS)

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

JWDemoHttp.hex : .depend Makefile JWDemoHttp.elf
	$(OBJCOPY) JWDemoHttp.elf -O ihex JWDemoHttp.hex
	@echo "Length is " `grep __"end_of_text__ = ." *.map | cut -b 17-35` "bytes"

JWDemoHttp.elf : .depend Makefile $(ARM_OBJ) $(COMMON)/common.a $(CRT0) $(LDSCRIPT)
	$(CC) $(CFLAGS) $(ARM_OBJ) -nostartfiles $(CRT0) $(LINKER_FLAGS)
	$(OBJDUMP) -d -S JWDemoHttp.elf >JWDemoHttp.lst
 
$(ARM_OBJ) : %.o : %.c Makefile .depend
	$(CC) -c $(CFLAGS) $< -o $@

#
#  Calculate sizes of all sections
#
sizes.csv : all
	find . -name \*.o | xargs arm-elf-size -A | ./size_to_csv.pl >sizes.csv

#
#  The .depend files contains the list of header files that the
#  various source files depend on.  By doing this, we'll only
#  rebuild the .o's that are affected by header files changing.
#
.depend:
	$(CC) $(CFLAGS) -M $(SRC_FILES) > .depend

#
#  Utility targets
#
.PHONY: tags
tags :
	@rm -f tags ctags
	find . -name \*.c -exec ctags -a {} \;
	find . -name \*.h -exec ctags -a {} \;

.PHONY: clean
clean :
	find . -name \*.o -exec rm -f {} \;
	find . -name .depend -exec rm -f {} \;
	rm -f *.map *.lst *.elf *.hex .depend $(COMMON)/common.a sizes.csv tags

#
#
#
ifeq (.depend,$(wildcard .depend))
include .depend
endif
