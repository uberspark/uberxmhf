#
#  $Id: Makefile 42 2008-10-04 18:40:36Z jcw $
#  $Revision: 42 $
#  $Author: jcw $
#  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
#  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/swi/Makefile $
#

SRC_FILES=swi.c
ASMSRC_FILES=swidispatch.s

#
# Define all object files.
#
ARM_OBJ = $(SRC_FILES:.c=.o)
ARM_ASMOBJ = $(ASMSRC_FILES:.s=.o)

.PHONY: all
all: $(ARM_OBJ) $(ARM_ASMOBJ)

$(ARM_OBJ) : %.o : %.c Makefile .depend
	$(CC) -c $(CFLAGS) $< -o $@
	$(AR) rc $(COMMON)/common.a $@

$(ARM_ASMOBJ) : %.o : %.s Makefile .depend
	$(CC) -c $(CFLAGS) $< -o $@
	$(AR) rc $(COMMON)/common.a $@

#
#  The .depend files contains the list of header files that the
#  various source files depend on.  By doing this, we'll only
#  rebuild the .o's that are affected by header files changing.
#
.depend:
			$(CC) $(CFLAGS) -M $(SRC_FILES) > .depend

ifeq (.depend,$(wildcard .depend))
include .depend
endif
