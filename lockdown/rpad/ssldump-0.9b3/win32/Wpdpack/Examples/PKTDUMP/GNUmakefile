# Makefile for cygwin gcc
# Nate Lawson <nate@rootlabs.com>

PCAP_PATH = ../../lib
CFLAGS = -g -O -mno-cygwin -I ../../include

OBJS = Pktdump.o
LIBS = -L ${PCAP_PATH} -lwpcap

all: ${OBJS}
	${CC} ${CFLAGS} -o pktdump.exe ${OBJS} ${LIBS}

clean:
	rm -f ${OBJS} pktdump.exe

.c.o:
	${CC} ${CFLAGS} -c -o $*.o $<
