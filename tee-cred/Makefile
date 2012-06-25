
export CROSS=
#CROSS=i686-pc-mingw32-
export PKG_CONFIG=pkg-config
export CC:=gcc
export LD:=ld
export OBJCOPY:=objcopy
export NM:=nm
export CC:=$(CROSS)$(CC)
export LD:=$(CROSS)$(LD)
export PKG_CONFIG:=$(CROSS)$(PKG_CONFIG)
export OBJCOPY:=$(CROSS)$(OBJCOPY)
export NM:=$(CROSS)$(NM)

#export CFLAGS+=-g -Wall -Werror -I.
export CFLAGS+=-g -Wall -I.
#export LDFLAGS+=--static
#export CFLAGS+=-DUSERSPACE_ONLY=1

export PAL_CFLAGS+=-g -Wall -Werror -I. -UWINDOWS -UWIN32 -U_WIN32

all: tee-cred

tee-cred:
	cd src; $(MAKE)

clean:
	cd src; $(MAKE) clean
