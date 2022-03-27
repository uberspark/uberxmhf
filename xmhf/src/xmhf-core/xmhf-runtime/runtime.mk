# Common makefile rules for components under xmhf-runtime
# author: Eric Li (xiaoyili@andrew.cmu.edu)
#
# These variables should have been already defined
#   C_SOURCES: .c files needed by secure loader / runtime
#   AS_SOURCES: .S files needed by secure loader / runtime
#   C_SOURCES_BL: .c files needed by boot loader when runtime is amd64
#   AS_SOURCES_BL: .S files needed by boot loader when runtime is amd64
#   EXTRA_CLEAN: files to be cleaned other than OBJECTS and OBJECTS_BL
#
# This file will define these variables
#   OBJECTS: .o files needed by secure loader / runtime
#   OBJECTS_BL: .o files needed by boot loader when runtime is amd64
#
# This file will define these targets
#   all: the default target, contains OBJECTS and OBJECTS_BL
#   *.o: built for secure loader / runtime
#   *.i386.o: built for boot loader when runtime is amd64
#   clean: remove object files and EXTRA_CLEAN

_AS_OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
_C_OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))
OBJECTS = $(_AS_OBJECTS) $(_C_OBJECTS)
OBJECTS_BL =

.PHONY: all
all: $(OBJECTS)

# TODO: Review whether I_SOURCES contains all header files
I_SOURCES = $(wildcard $(INCLUDEDIR)/*.h)

M_SOURCES = Makefile ../Makefile ../../Makefile

$(_AS_OBJECTS): %.o: %.S $(I_SOURCES) $(M_SOURCES)
	$(CC) -c $(ASFLAGS) -o $@ $<
$(_C_OBJECTS): %.o: %.c $(I_SOURCES) $(M_SOURCES)
	$(CC) -c $(CFLAGS) -o $@ $<

# TODO: Workaround to compile i386 bootloader
ifeq ($(TARGET_SUBARCH), amd64)
_AS_OBJECTS_BL = $(patsubst %.S, %.i386.o, $(AS_SOURCES_BL))
_C_OBJECTS_BL = $(patsubst %.c, %.i386.o, $(C_SOURCES_BL))
OBJECTS_BL = $(_AS_OBJECTS_BL) $(_C_OBJECTS_BL)

all: $(OBJECTS_BL)

$(_AS_OBJECTS_BL): %.i386.o: %.S $(I_SOURCES) $(M_SOURCES)
	$(CC32) -c $(BASFLAGS) -o $@ $<
$(_C_OBJECTS_BL): %.i386.o: %.c $(I_SOURCES) $(M_SOURCES)
	$(CC32) -c $(BCFLAGS) -o $@ $<
endif

.PHONY: clean
clean:
	$(RM) -rf $(OBJECTS) $(OBJECTS_BL) $(EXTRA_CLEAN)

