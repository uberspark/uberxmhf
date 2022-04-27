#top-level Makefile for rich guest app, aprvexec (rgapp-aprvexec)
# author: amit vasudevan (amitvasudevan@acm.org)

.PHONY: all
all: 
	gcc -m32 rgapp-aprvexec.c rgapp-aprvexecsup.S -o rgapp-aprvexec

.PHONY: clean
clean:
	rm -f rgapp-aprvexec
	rm -f *.o
	