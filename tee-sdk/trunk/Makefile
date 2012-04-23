# target platform when building a compiler (tsvc)
TARGET=i586-tsvc
# machine where software will run (for pal-code)
TSVC_HOST=$(TARGET)
# machine where software will run (for reg-world code)
HOST=i686-pc-linux-gnu
# machine where software will be built
BUILD=i686-pc-linux-gnu
# where reg-world software will be installed
PREFIX=/usr/local
# where pal software (libraries, headers, etc.) will be installed
TSVC_SYSROOT=$(PREFIX)/$(TSVC_HOST)

all: toolchain newlib tz_host tz_cross

toolchain:
	cd toolchain && \
	./autogen.sh && \
	./configure --prefix=$(PREFIX) --host=$(HOST) --target=$(TARGET) --build=$(BUILD) && \
	make && \
	make install

newlib: toolchain
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd ports/newlib && \
	PREFIX=$(PREFIX) HOST=$(TSVC_HOST) ./build.sh

tz_autoreconf:
	cd tz && autoreconf -i

tz_host: tz_autoreconf
	export PKG_CONFIG_PATH=$(PREFIX)/lib/pkgconfig && \
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd tz && \
	mkdir -p build-$(HOST) && \
	cd build-$(HOST) && \
	../configure --prefix=$(PREFIX) --host=$(HOST) --build=$(BUILD) && \
	make && \
	make install

tz_cross: tz_autoreconf toolchain newlib
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd tz && \
	mkdir -p build-$(TSVC_HOST) && \
	cd build-$(TSVC_HOST) && \
	../configure --prefix=$(TSVC_SYSROOT)/usr --host=$(TSVC_HOST) --build=$(BUILD) && \
	make && \
	make install

openssl: toolchain newlib
	export PATH=$(PREFIX)/bin:$(PATH) && \
	cd ports/openssl && \
	PREFIX=$(TSVC_SYSROOT)/usr HOST=$(TSVC_HOST) ./build.sh

.PHONY: toolchain newlib openssl tz_host tz_cross tz_autoreconf
