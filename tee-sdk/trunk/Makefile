HOST=i586-tsvc
BUILD=i686-pc-linux-gnu
PREFIX=/usr/local
SYSROOT=$(PREFIX)/$(HOST)

all: toolchain newlib tz_host tz_cross

toolchain:
	cd toolchain && \
	autoreconf -i && \
	HOST=$(HOST) ./configure --prefix=$(PREFIX) && \
	make && \
	sudo make install

newlib: toolchain
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd ports/newlib && \
	PREFIX=$(PREFIX) HOST=$(HOST) ./build.sh

tz_autoreconf:
	cd tz && autoreconf -i

tz_host: tz_autoreconf
	cd tz && \
	mkdir build-host && \
	cd build-host && \
	../configure --prefix=$(PREFIX) && \
	make && \
	sudo make install

tz_cross: tz_autoreconf toolchain newlib
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd tz && \
	mkdir build-cross && \
	cd build-cross && \
	../configure --prefix=$(SYSROOT)/usr --host=$(HOST) --build=$(BUILD) && \
	make && \
	sudo make install

openssl: toolchain newlib
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd ports/openssl && \
	PREFIX=$(SYSROOT)/usr HOST=$(HOST) ./build.sh

.PHONY: toolchain newlib openssl tz_host tz_cross tz_autoreconf
