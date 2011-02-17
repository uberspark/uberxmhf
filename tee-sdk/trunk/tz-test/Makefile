# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CC=gcc
LD=ld
RM=rm -f

#linker script
LINK_SCRIPT = inject.ld 

TESTS=-DTEST_VMMCALL -DTEST_WITHOUTPARAM -DTEST_PARAM -DTEST_SEAL -DTEST_QUOTE

# for debug
CFLAGS=-g $(TESTS) -DnotPERFCPIT -fno-stack-protector -fno-jump-tables -Wall -I../include
#CFLAGS+=-I/usr/include 
# for run
#CFLAGS=-O2 -DnotPERFCPIT -fno-stack-protector 

# oject files
#OBJS = $(patsubst %.c, %.o, $(SRCS))
OBJS = test.o pals.o

# source .c file
#SRCS = test.c foo.c 

#I_SOURCES = $(wildcard *.h)

all: test

test:$(OBJS) ../src/libscode.a
	$(CC) $(CFLAGS) -T $(LINK_SCRIPT) -L../src $(OBJS) -lscode -o $@

#.PHONY: all
#all: $(OBJS)
#	$(LD) --oformat=pe-i386 -T $(LINK_SCRIPT) -L/usr/lib/libc.a -o test.exe $(OBJS)

#%.o:%.c $(I_SOURCES)
#	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* test test.D
