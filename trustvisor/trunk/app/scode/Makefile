# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CC=gcc
RM=rm -f

#linker script
LINK_SCRIPT = defaultld.ld 

# for debug
CFLAGS=-g -O2 -DnotPERFCPIT -fno-stack-protector 
# for run
#CFLAGS=-O2 -DnotPERFCPIT -fno-stack-protector 

# oject files
C_OBJS = slb.o \
		 foo.o \
		 pm.o \
		 passwd.o 

# source .c file
SRCS = slb.c \

slb:$(C_OBJS)
	$(CC) $(CFLAGS) -T $(LINK_SCRIPT) -o $@ $(C_OBJS)
clean:
	$(RM) .*.cmd *.o *.ko *~ -r .tmp* slb slb.D
