C_SOURCES = $(wildcard *.c)
INCLUDES = $(wildcard *.h)

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard *.h)

CFLAGS += -I../app/include -I../emhfcore/x86/include -I../emhfcore/libemhfutil/include -I. -nostdinc

# In the future hopefully there will be a more suitable place
# to put this than APPOBJECTSDIR. Path of least resistance for
# now, especially in the face of major EMHF build refactoring
THE_ARCHIVE = $(APPOBJECTSDIR)/tv_utpm.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	mkdir -p $(APPOBJECTSDIR)
	$(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c $(C_SOURCES) $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) -f $(OBJECTS)
	$(RM) -f $(THE_ARCHIVE)


.PHONY: install
install:
	install -d /usr/local/lib/pkgconfig
	install --mode=644 tv_utpm.pc /usr/local/lib/pkgconfig
	install --mode=644 $(THE_ARCHIVE) /usr/local/lib/
