#-------------------------------------------------------------------------------
# makefile for XMHF apps
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 
C_SOURCES = appmain.c
I_SOURCES =  $(wildcard ./*.h)

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

CFLAGS += -I.

# LLC flags
LLC_ATTR = -3dnow,-3dnowa,-64bit,-64bit-mode,-adx,-aes,-atom,-avx,-avx2,-bmi,-bmi2,-cmpxchg16b,-f16c,-hle,-lea-sp,-lea-uses-ag,-lzcnt,-mmx,-movbe,-pclmul,-popcnt,-prfchw,-rdrand,-rdseed,-rtm,-slow-bt-mem,-sse,-sse3,-sse41,-sse42,-sse4a,-sse3,-vector-unaligned-mem,-xop

# targets
.PHONY: all
all: $(OBJECTS) 

%.o: %.c   
	@echo Building "$(@F)" from "$<" 
	$(CC) -S -emit-llvm $(CFLAGS) $< -o $(@F).ll
	llc -O=0 -march=x86 -mcpu=corei7 -mattr=$(LLC_ATTR) $(@F).ll
	$(CC) -c $(CFLAGS) $(@F).s -o $(@F)

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	$(RM) -rf *.s
	$(RM) -rf *.ll
	
