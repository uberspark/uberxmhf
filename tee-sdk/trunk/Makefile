HOST=i586-tsvc
BUILD=i686-pc-linux-gnu
PREFIX=/usr/local
SYSROOT=$(PREFIX)/$(HOST)

all: toolchain newlib tz_host tz_cross

toolchain:
	cd toolchain; \
	autoreconf -i; \
	HOST=$(HOST) SYSROOT=$(SYSROOT) ./configure --prefix=$(PREFIX); \
	make; \
	sudo make install

newlib: toolchain
	cd ports/newlib; \
	PREFIX=$(PREFIX) HOST=$(HOST) ./build.sh

tz_host:
	cd tz; \
	mkdir build-host; \
	cd build-host; \
	../configure --prefix=$(PREFIX); \
	make; \
	sudo make install

tz_cross: toolchain newlib
	cd tz; \
	mkdir build-cross; \
	cd build-cross; \
	../configure --prefix=$(PREFIX) --host=$(HOST) --build=$(BUILD); \
	make; \
	sudo make install

openssl: toolchain newlib
	cd ports/openssl; \
	PREFIX=$(PREFIX) HOST=$(HOST) ./build.sh

.PHONY: toolchain newlib openssl tz_host tz_cross
