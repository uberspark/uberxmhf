
all: pehashdump 

pehashdump: sha1.h pehashdump.c sha1.c 
	$(CC) $(HOSTCFLAGS) -I. -I../../../../../../tools/libtomcrypt-1.17/src/headers/ pehashdump.c sha1.c -o pehashdump

clean:
	$(RM) -rf *.o
	$(RM) -rf pehashdump
