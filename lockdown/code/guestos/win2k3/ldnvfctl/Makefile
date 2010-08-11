# app defs
EXE = ldnvfctl.exe
LIBUSB =  ./libusb-win32-device-bin-0.1.12.1
export LDNVFCTL_INSTALLDIR := /cygdrive/e/vpcvms/sharedfolder

# tool defs
CFLAGS = -W -Wall -g -I$(LIBUSB)/include
LIBS = $(LIBUSB)/lib/gcc/libusb.a /usr/lib/w32api/libpowrprof.a /usr/lib/w32api/libkernel32.a

all: $(EXE)
	cp ./ldnvfctl.exe $(LDNVFCTL_INSTALLDIR)/ldnvfctl.exe 
	cp ./libusb0.dll $(LDNVFCTL_INSTALLDIR)/libusb0.dll
	cp ./cyggcc_s-1.dll $(LDNVFCTL_INSTALLDIR)/.
	cp ./cygwin1.dll $(LDNVFCTL_INSTALLDIR)/.

$(EXE): main.o
	$(CC) -o $(EXE) $< $(LIBS)

clean:
	$(RM) $(EXE) main.o 
	
	
