PKGCONFIG_DEPS=tee-sdk-svc-tv tee-sdk-app
PKG_CFLAGS=$(shell pkg-config --cflags $(PKGCONFIG_DEPS))
PKG_LDLIBS=$(shell pkg-config --libs --static $(PKGCONFIG_DEPS))

CFLAGS+=$(PKG_CFLAGS)
LDLIBS+=$(PKG_LDLIBS)

CFLAGS+=-Wall
CFLAGS+=-g

LINK=$(CC) $(LDFLAGS) -o $@ $^ $(LDLIBS) 

all: secret-fun.bin load-code seal-code

seal-code: sealed-code-pal.o sealed-code-pal-interface.o common.o seal-code.o
	$(LINK)

load-code: sealed-code-pal.o sealed-code-pal-interface.o common.o load-code.o
	$(LINK)

secret-fun: secret-fun.c
	$(CC) --static -fPIC -nostdlib -o $@ $? -Wall
secret-fun.bin: secret-fun
	objcopy -O binary -j .text -j .rodata ./secret-fun secret-fun.bin

clean:
	$(RM) *.o seal-code load-code secret-fun secret-fun.bin