# Makefile made with help from http://www.hsrl.rutgers.edu/ug/make_help.html
# $@ is the name of the file to be made.
# $? is the names of the changed dependents. 
# $< the name of the related file that caused the action.
# $* the prefix shared by target and dependent files. 

# object files
#SRCS = src/tz.c src/marshal.c
#I_SOURCES = $(wildcard include/*.h) $(wildcard src/*.h)
#OBJS = $(patsubst %.c, %.o, $(SRCS))
#OBJS += dev/dev.o

srcdir ?= .
override CFLAGS += -I$(srcdir)/include/

all : libtz.a
libtz.a: libtz.a(src/tz.o src/marshal.o)
clean:
	$(RM) ./libtz.a

# put everything locally by default for now
DESTDIR = $(srcdir)/../dist/

# Generally, $(exec_prefix) is used for directories that contain
# machine-specific files (such as executables and subroutine
# libraries), while $(prefix) is used directly for other directories.
prefix = /usr/local/
exec_prefix = $(prefix)

# The directory for installing executable programs that users can run
bindir = $(exec_prefix)/bin

# The directory for installing executable programs that can be run
# from the shell, but are only generally useful to system
# administrators.
sbindir = $(exec_prefix)/sbin

# The directory for installing executable programs to be run by other
# programs rather than by users.
libexecdir = $(exec_prefix)/libexec

# The root of the directory tree for read-only
# architecture-independent data files.
datarootdir = $(prefix)/share

# The directory for installing idiosyncratic read-only
# architecture-independent data files for this program.
datadir = $(datarootdir)

# The directory for installing read-only data files that pertain to a
# single machine–that is to say, files for configuring a host.
sysconfdir = $(prefix)/etc

# The directory for installing architecture-independent data files
# which the programs modify while they run.
sharedstatedir = $(prefix)/com

# The directory for installing data files which the programs modify
# while they run, and that pertain to one specific machine.
localstatedir = $(prefix)/var

# The directory for installing header files to be included by user
# programs with the C ‘#include’ preprocessor directive.
includedir = $(prefix)/include

# The directory for object files and libraries of object code.
libdir = $(exec_prefix)/lib

install:
	echo $(prefix)

.PHONY: all clean install

