# app defs
EXE = main.exe
LIBUSB =  ./libusb-win32-device-bin-0.1.12.1

# tool defs
CFLAGS = -W -Wall -g -I$(LIBUSB)/include
LIBS = $(LIBUSB)/lib/gcc/libusb.a /usr/lib/w32api/libpowrprof.a

all: $(EXE)

$(EXE): main.o
	$(CC) -o $(EXE) $< $(LIBS)

clean:
	$(RM) $(EXE) main.o 
	
	
