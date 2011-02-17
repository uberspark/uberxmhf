# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CC=gcc
LD=ld
RM=rm -f

# config options. enable\disable these
#IS_WINDOWS=-DIS_WINDOWS
IS_WINDOWS=
IS_VMX=-DIS_VMX
#IS_VMX=

# for debug
CFLAGS=-g $(IS_WINDOWS) $(IS_VMX) -DnotPERFCPIT -fno-stack-protector -Wall -I../include

# object files
#OBJS = $(patsubst %.c, %.o, $(SRCS))
OBJS = scode.o trustzone.o tzdev_trustvisor.o marshal.o

# source .c file
#SRCS = scode.o

#I_SOURCES = $(wildcard *.h)

libscode.a:scode.o trustzone.o tzdev_trustvisor.o marshal.o
	ar rcs $@ $(OBJS)

#.PHONY: all
#all: $(OBJS)
#	$(LD) --oformat=pe-i386 -T $(LINK_SCRIPT) -L/usr/lib/libc.a -o slb.exe $(OBJS)

#%.o:%.c $(I_SOURCES)
#	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* libscode.a
 