# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CC=gcc
RM=rm -f

CFLAGS=-O2


# object files
C_OBJS = ltstate.o
# source .c file
SRCS = ltstate.c

ltstate:$(C_OBJS)
	$(CC) -o $@ $(C_OBJS)

clean:
	$(RM) .*.cmd *.mod.c *.o *.ko *~ -r .tmp* ltstate
