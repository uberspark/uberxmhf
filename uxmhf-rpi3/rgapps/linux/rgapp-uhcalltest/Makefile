#top-level Makefile for usr mode application to test hypercall
# author: amit vasudevan (amitvasudevan@acm.org)

.PHONY: all
all: 
	arm-linux-gnueabihf-gcc uhcalltest.c -o uhcalltest

.PHONY: clean
clean:
	rm -f uhcalltest
	rm -f *.o
	