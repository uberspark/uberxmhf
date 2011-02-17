include ../Makefile.inc

DIRS = tv
OBJS = $(patsubst %, %/dev.o, $(DIRS))

all: dev.o

dev.o: $(OBJS)
	$(LD) -r -o dev.o $(OBJS)

%/dev.o:
	cd $(dir $@); $(MAKE) $(MFLAGS)

clean:
	-$(RM) dev.o
	-for d in $(DIRS); do (cd $$d; $(MAKE) clean); done