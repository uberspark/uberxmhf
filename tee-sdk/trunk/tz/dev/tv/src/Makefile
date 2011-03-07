REL=../..
include $(REL)/Makefile.inc

SRCS = src/scode.c src/tv.c
I_SOURCES = $(wildcard include/*.h) $(wildcard src/*.h) $(wildcard ../../include/*)
OBJS = $(patsubst %.c, %.o, $(SRCS))

all: dev.o

dev.o: $(OBJS)
	$(LD) -r -o dev.o $(OBJS)

%.o:%.c $(I_SOURCES)
	$(CC) -c $(CFLAGS) -I../../include -Iinclude/ -I$(REL)/../svcapi -o $@ $<

clean:
	$(RM) $(OBJS) dev.o
