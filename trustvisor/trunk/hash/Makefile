
all: binoffset sha1

visor: binoffset sha1
	./visor.pl $(BASEDIR)/$(B_DIR)/$(TARGET) > hashvisor.c 2> /dev/null
	$(RM) -f $(BASEDIR)/$(B_DIR)/visor.o $(BASEDIR)/$(B_DIR)/$(TARGET)*

sha1: sha1.h sha1.c binoffset
	$(CC) $(HOSTCFLAGS) -I. $@.c -o $@ 

binoffset:
	$(CC) $(HOSTCFLAGS) -I. $@.c -o $@ 

clean:
	$(RM) -f sha1 binoffset
