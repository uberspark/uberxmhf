
all: pehashdump 

pehashdump: sha1.h pehashdump.c 
	$(CC) $(HOSTCFLAGS) -I. $@.c -o $@ 

clean:
	$(RM) -rf *.o
	$(RM) -rf pehashdump
