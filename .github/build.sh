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

set -e

# Information about compiler's platform
LINUX_BASE=""					# DEB or RPM
LINUX_BIT=$(getconf LONG_BIT)	# 32 or 64

# Information about XMHF
APPROOT="hypapps/trustvisor"
SUBARCH=""
DRT="n"
DMAP="n"
QEMU="y"
AMD64MEM="0x140000000"
DRY_RUN="n"

# Determine LINUX_BASE (may not be 100% correct all the time)
if [ -f "/etc/debian_version" ]; then
	# DEB-based Linux (e.g. Debian, Ubuntu)
	LINUX_BASE="DEB"
else if [ -f "/etc/redhat-release" ]; then
	# RPM-based Linux (e.g. Fedora)
	LINUX_BASE="RPM"
else
	echo 'Error: build.sh does not know about OS it is running on.'; exit 1
fi; fi

# Check LINUX_BIT
case "$LINUX_BIT" in
	32)
		;;
	64)
		;;
	*)
		echo 'Error: unknown result from `getconf LONG_BIT`'; exit 1
		;;
esac

# Determine SUBARCH
case "$1" in
	i386)
		SUBARCH="i386"
		;;
	amd64)
		SUBARCH="amd64"
		;;
	*)
		echo 'Error: subarch incorrect, should be i386 or amd64'; exit 1
		;;
esac
shift

# Process other arguments
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
			echo "Error: unknown argument $1"; exit 1
			;;
	esac
	shift 
done

# Build configure arguments
CONFIGURE_ARGS="--with-approot=$APPROOT"
CONFIGURE_ARGS="${CONFIGURE_ARGS} --enable-debug-symbols"

if [ "$SUBARCH" == "i386" ]; then
	# Building i386 XMHF
	if [ "$LINUX_BASE" == "DEB" -a "$LINUX_BIT" == "64" ]; then
		# Building on amd64 Debian
		CONFIGURE_ARGS="${CONFIGURE_ARGS} CC=i686-linux-gnu-gcc"
		CONFIGURE_ARGS="${CONFIGURE_ARGS} LD=i686-linux-gnu-ld"
	fi
else if [ "$SUBARCH" == "amd64" ]; then
	# Building amd64 XMHF
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --with-target-subarch=amd64"
	CONFIGURE_ARGS="${CONFIGURE_ARGS} --with-amd64-max-phys-addr=$AMD64MEM"
	if [ "$LINUX_BASE" == "DEB" -a "$LINUX_BIT" == "32" ]; then
		# Building on i386 Debian
		CONFIGURE_ARGS="${CONFIGURE_ARGS} CC=x86_64-linux-gnu-gcc"
		CONFIGURE_ARGS="${CONFIGURE_ARGS} LD=x86_64-linux-gnu-ld"
	fi
else
	echo 'Error: unexpected $SUBARCH'; exit 1
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

# Output configure arguments, if `-n`
if [ "$DRY_RUN" == "y" ]; then
	set +x
	echo $'\n'"./autogen.sh; ./configure ${CONFIGURE_ARGS}"$'\n'
	exit 0
fi

# Build
./autogen.sh
./configure ${CONFIGURE_ARGS}
make -j "$(nproc)"

