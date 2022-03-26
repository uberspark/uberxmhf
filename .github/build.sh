#!/bin/bash
# Usage: build.sh subarch [arguments [...]]
# subarch: i386 or amd64
# arguments:
#   --drt: enable DRT (--disable-drt)
#   --dmap: enable DMAP (--disable-dmap)
#   --no-dbg: do not use QEMU debug workarounds (--enable-debug-qemu)
#   --app APP: set hypapp, default is "hypapps/trustvisor" (--with-approot)
#   --mem MEM: if amd64, set physical memory, default is 0x140000000 (5GiB)
#   release: equivalent to --drt --dmap --no-dbg (For GitHub actions)
#   debug: ignored (For GitHub actions)
#   -n: print autogen.sh and configure options, do not run them

set -xe

APPROOT="hypapps/trustvisor"
SUBARCH=""
DRT="n"
DMAP="n"
QEMU="y"
AMD64MEM="0x140000000"
DRY_RUN="n"

case "$1" in
	i386)
		SUBARCH="i386"
		;;
	amd64)
		SUBARCH="amd64"
		;;
	*)
		echo 'Subarch incorrect, should be i386 or amd64'; exit 1
		;;
esac
shift

while [ "$#" -gt 0 ]; do
	case "$1" in
		--drt)
			DRT="y"
			;;
		--dmap)
			DMAP="y"
			;;
		--no-dbg)
			QEMU="n"
			;;
		--app)
			APPROOT="$2"
			shift 2
			;;
		--mem)
			AMD64MEM="$2"
			shift 2
			;;
		release)
			# For GitHub actions
			DRT="y"
			DMAP="y"
			QEMU="n"
			;;
		debug)
			# For GitHub actions
			;;
		-n)
			DRY_RUN="y"
			;;
		*)
			echo "Unknown argument $1"; exit 1
			;;
	esac
	shift 
done

CONFIGURE_ARGS="--with-approot=$APPROOT"
CONFIGURE_ARGS="${CONFIGURE_ARGS} --enable-debug-symbols"

if [ "$SUBARCH" == "i386" ]; then
	CONFIGURE_ARGS="${CONFIGURE_ARGS} CC=i686-linux-gnu-gcc"
	CONFIGURE_ARGS="${CONFIGURE_ARGS} LD=i686-linux-gnu-ld"
else if [ "$SUBARCH" == "amd64" ]; then
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --with-target-subarch=amd64"
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --with-amd64-max-phys-addr=$AMD64MEM"
else
	echo 'Unexpected $SUBARCH'; exit 1
fi; fi

if [ "$DRT" == "n" ]; then
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --disable-drt"
fi

if [ "$DMAP" == "n" ]; then
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --disable-dmap"
fi

if [ "$QEMU" == "y" ]; then
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --enable-debug-qemu"
fi

if [ "$DRY_RUN" == "y" ]; then
	set +x
	echo $'\n'"./autogen.sh; ./configure ${CONFIGURE_ARGS}"$'\n'
	exit 0
fi

./autogen.sh
./configure ${CONFIGURE_ARGS}
make -j "$(nproc)"

