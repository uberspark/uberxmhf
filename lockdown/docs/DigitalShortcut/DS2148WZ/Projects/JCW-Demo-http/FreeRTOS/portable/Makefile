#
#  $Id: Makefile 42 2008-10-04 18:40:36Z jcw $
#  $Revision: 42 $
#  $Author: jcw $
#  $Date: 2008-10-04 14:40:36 -0400 (Sat, 04 Oct 2008) $
#  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/FreeRTOS/portable/Makefile $
#

#
# Define all object files.
#
SUBDIRS=GCC MemMang

.PHONY: all
all : subdirs

.PHONY: subdirs $(SUBDIRS)

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@
