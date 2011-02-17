REL=../..
include $(REL)/Makefile.inc

SRCS = src/scode.c src/tv.c
I_SOURCES = $(wildcard include/*.h) $(wildcard src/*.h) $(wildcard ../../include/*)
OBJS = $(patsubst %.c, %.o, $(SRCS))

all: dev.a

dev.a: $(OBJS)
	ar rcs $@ $(OBJS) $(OBJLIBS)		

%.o:%.c $(I_SOURCES)
	$(CC) -c $(CFLAGS) -I../../include -Iinclude/ -o $@ $<

clean:
	$(RM) $(OBJS) dev.a
