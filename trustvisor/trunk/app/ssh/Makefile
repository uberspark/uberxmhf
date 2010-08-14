# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

CC=gcc -g
RM=rm -f

CFLAGS=-O2 -DnotPERFCRIT -fno-stack-protector

#linker script
LINK_SCRIPT = defaultld.ld 
#LINK_SCRIPT = readpass.ld

# oject files
C_OBJS = malloc.o bignum.o puttymem.o rsa.o sha1.o passwd.o scode.o main.o
# source .c file
SRCS = main.c
slb.o:$(C_OBJS)
	$(CC) -T $(LINK_SCRIPT) -o $@ $(C_OBJS)
#	ld --oformat binary -T $(LINK_SCRIPT) -o $@ $(C_OBJS) $(LIB_OBJS) lc
#	ld -T $(LINK_SCRIPT) -o $@ $(LIB_OBJS) $(C_OBJS) -lc 
clean:
	$(RM) .*.cmd *.mod.c *.o *.ko *~ -r .tmp*
