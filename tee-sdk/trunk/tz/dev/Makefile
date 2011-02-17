include ../Makefile.inc

DIRS = tv
OBJLIBS = $(patsubst %, %/dev.a, $(DIRS))

all: libdev.a

libdev.a: $(OBJLIBS)
	ar rcs $@ $(OBJLIBS)

%/dev.a:
	cd $(dir $@); $(MAKE) $(MFLAGS)

clean:
	-$(RM) libdev.a
	-for d in $(DIRS); do (cd $$d; $(MAKE) clean); done