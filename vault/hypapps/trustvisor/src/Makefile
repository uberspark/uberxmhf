#-------------------------------------------------------------------------------
# makefile for XMHF apps
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES = 
C_SOURCES = $(wildcard *.c)
I_SOURCES =  $(wildcard ./include/*.h)

OBJECTS = $(patsubst %.S, %.o, $(AS_SOURCES))
OBJECTS += $(patsubst %.c, %.o, $(C_SOURCES))

CFLAGS += -I./include

# app-specific configuration options
export LDN_TV_INTEGRATION := n

#lockdown-trustvisor integration demo
ifeq ($(LDN_TV_INTEGRATION), y)
  CFLAGS += -D__LDN_TV_INTEGRATION__
endif


#-----------------------------------------------------------------------
# build targets
# all, install, install-dev, test, clean and distclean

.PHONY: all
all: $(OBJECTS) 

%.o: %.S $(I_SOURCES) Makefile ../Makefile 
	$(CC) -c $(ASFLAGS) -o $@ $<
%.o: %.c $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

# nothing that is trustvisor specific
.PHONY: install
install: 

# install trustvisor development components
.PHONY: install-dev
install-dev:
	install -d $(DESTDIR)$(pkgconfigdir)
	install --mode=644 ../trustvisor.pc $(DESTDIR)$(pkgconfigdir)
	install -d $(DESTDIR)$(includedir)/trustvisor
	install ./include/trustvisor.h $(DESTDIR)$(includedir)/trustvisor
	install /usr/local/include/xmhf/libbaremetal/libtv_utpm/include/tv_utpm.h $(DESTDIR)$(includedir)/trustvisor

.PHONY: test
test:
	cd test && $(MAKE) -w all

.PHONY: clean 
clean: 
	$(RM) -rf *.o
	cd test && $(MAKE) -w clean

# nothing that is trustvisor specific
.PHONY: distclean
distclean: 
