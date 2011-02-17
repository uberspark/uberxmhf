REL=.
include Makefile.inc

# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

# object files
SRCS = src/tz.c src/marshal.c
I_SOURCES = $(wildcard include/*.h) $(wildcard src/*.h)
OBJS = $(patsubst %.c, %.o, $(SRCS))
OBJS += dev/dev.o

all : libtz.a

libtz.a: $(OBJS)
	ar rcs $@ $(OBJS)

dev/dev.o:
	cd dev; $(MAKE) $(MFLAGS)

clean:
	$(RM) libtz.a
	cd dev; $(MAKE) $(MFLAGS) clean

%.o:%.c $(I_SOURCES)
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean