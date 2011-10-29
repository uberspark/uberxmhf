C_SOURCES = $(wildcard *.c)

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

I_SOURCES =  $(wildcard ./include/*.h)

CFLAGS += -I./include -nostdinc

# In the future hopefully there will be a more suitable place
# to put this than APPOBJECTSDIR. Path of least resistance for
# now, especially in the face of major EMHF build refactoring
THE_ARCHIVE = libemhfc.a

# targets
.PHONY: all
all: $(THE_ARCHIVE)

$(THE_ARCHIVE): $(OBJECTS)
	$(AR) -rcs $(THE_ARCHIVE) $(OBJECTS)

%.o: %.c $(C_SOURCES) $(I_SOURCES) Makefile ../Makefile
	$(CC) -c $(CFLAGS) -o $@ $<

.PHONY: clean
clean:
	$(RM) -f $(OBJECTS)
	$(RM) -f $(THE_ARCHIVE)


.PHONY: install
install:
	install -d $(DESTDIR)$(pkgconfigdir)
	install --mode=644 tv_utpm.pc $(DESTDIR)$(pkgconfigdir)
	install --mode=644 $(THE_ARCHIVE) $(DESTDIR)$(libdir)
