OBJS=svcapi.o
INCLUDES=-I../tz/dev/tv/include/
IS_VMX=-DIS_VMX
CFLAGS=$(IS_VMX) -g $(INCLUDES)
RM=rm -f

all: libsvcapi.a

libsvcapi.a: $(OBJS)
	ar rcs $@ $<

%.o:%.c $(I_SOURCES)
	$(CC) -c $(CFLAGS) -o $@ $<

clean:
	$(RM) libsvcapi.a $(OBJS)
