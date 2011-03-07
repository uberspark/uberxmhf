# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CC=gcc
LD=ld
RM=rm -f

#linker script
LINK_SCRIPT = defaultld.ld 

# for debug
CFLAGS=-g -DnotPERFCPIT -fno-stack-protector
#CFLAGS+=-I/usr/include 
# for run
#CFLAGS=-O2 -DnotPERFCPIT -fno-stack-protector 

# oject files
#OBJS = $(patsubst %.c, %.o, $(SRCS))
OBJS = foo.o slb.o

# source .c file
#SRCS = slb.c foo.c 

#I_SOURCES = $(wildcard *.h)

slb:$(OBJS)
	$(CC) $(CFLAGS) -T $(LINK_SCRIPT) -o $@ $(OBJS)

#.PHONY: all
#all: $(OBJS)
#	$(LD) --oformat=pe-i386 -T $(LINK_SCRIPT) -L/usr/lib/libc.a -o slb.exe $(OBJS)

#%.o:%.c $(I_SOURCES)
#	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* slb slb.D
