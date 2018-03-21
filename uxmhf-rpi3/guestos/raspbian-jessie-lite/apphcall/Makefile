#top-level Makefile for usr mode application to test hypercall
# author: amit vasudevan (amitvasudevan@acm.org)

.PHONY: all
all: 
	arm-linux-gnueabihf-gcc apphcall.c -o apphcall

.PHONY: clean
clean:
	rm -f apphcall
	rm -f *.o
	