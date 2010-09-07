
all: sha1 

sha1: sha1.h sha1.c 
	$(CC) $(HOSTCFLAGS) -I. $@.c -o $@ 

clean:
	$(RM) -f sha1.exe
