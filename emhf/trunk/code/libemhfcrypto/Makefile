# source files
AS_SOURCES = $(wildcard *.S)
C_SOURCES = $(wildcard *.c)

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard $(INCLUDEDIR)/*.h)

# TODO: Inherit these from above; I don't like having to specify all of this here
CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
CFLAGS += -fno-stack-protector
CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement
CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal
CFLAGS += -Wcast-qual -Wsign-compare
CFLAGS += -Wno-bad-function-cast
CFLAGS += -Waggregate-return
CFLAGS += -Winline
CFLAGS += -m32 -march=k8
CFLAGS += -mno-mmx -mno-sse -mno-sse2 -mno-sse3 -mno-ssse3
CFLAGS += -mno-sse4.1 -mno-sse4.2 -mno-sse4 -mno-avx -mno-aes
CFLAGS += -mno-pclmul -mno-sse4a -mno-sse5 -mno-3dnow -mno-popcnt -mno-abm

CFLAGS += -nostdinc -I./include -I../libemhfc/include

THE_ARCHIVE = libemhfcrypto.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.S $(I_SOURCES) Makefile ../Makefile ../../../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile ../../../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) $(OBJECTS) $(THE_ARCHIVE)
