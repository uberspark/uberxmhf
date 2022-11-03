#!/bin/bash

set -xe

# Information about compiler's platform
LINUX_BASE=""					# DEB or RPM
LINUX_BIT=$(getconf LONG_BIT)	# 32 or 64

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
		echo 'Error: compiling on i386 Linux not supported yet'; exit 1
		;;
	64)
		;;
	*)
		echo 'Error: unknown result from `getconf LONG_BIT`'; exit 1
		;;
esac

PAL_DEMO_DIR="hypapps/trustvisor/pal_demo"
cd "$PAL_DEMO_DIR"

build () {
	local MAKE_ARGS=()
	if [ "$1" == "windows" ]; then
		MAKE_ARGS+=("WINDOWS=y")
		if [ "$2" == "i386" ]; then
			MAKE_ARGS+=("CC=i686-w64-mingw32-gcc" "LD=i686-w64-mingw32-ld")
		else if [ "$2" == "amd64" ]; then
			MAKE_ARGS+=("CC=x86_64-w64-mingw32-gcc" "LD=x86_64-w64-mingw32-ld")
		else
			echo '$2 incorrect, should be i386 or amd64'; return 1
		fi; fi
	else if [ "$1" == "linux" ]; then
		if [ "$2" == "i386" ]; then
			if [ "$LINUX_BASE" == "DEB" ]; then
				MAKE_ARGS+=("CC=i686-linux-gnu-gcc" "LD=i686-linux-gnu-ld")
			else
				MAKE_ARGS+=("I386=y")
			fi
		else if [ "$2" == "amd64" ]; then
			MAKE_ARGS+=()
		else
			echo '$2 incorrect, should be i386 or amd64'; return 1
		fi; fi
	else
		echo '$1 incorrect, should be windows or linux or all'; return 1
	fi; fi
	shift 2

	while [ "$#" -gt 0 ]; do
		case "$1" in
			"")
				;;
			"L1")
				;;
			"L2")
				MAKE_ARGS+=("VMCALL_OFFSET=0x50414c00U")
				;;
			*)
				echo "Error: unknown argument $1"; return 1
				;;
		esac
		shift 
	done

	make clean
	make -j "$(nproc)" "${MAKE_ARGS[@]}"
}

build_and_move () {
	build "$1" "$2" "$3"
	for i in main test test_args; do
		mv "${i}$5" "${i}$4$3$5"
	done
}

if [ "$1" == "all" ]; then
	for i in {main,test,test_args}{32,64}{,L2}{,.exe}; do
		rm -f $i
	done
	rm -f pal_demo.zip
	build_and_move linux   i386  "" 32 ""
	build_and_move linux   amd64 "" 64 ""
	build_and_move windows i386  "" 32 ".exe"
	build_and_move windows amd64 "" 64 ".exe"
	build_and_move linux   i386  L2 32 ""
	build_and_move linux   amd64 L2 64 ""
	build_and_move windows i386  L2 32 ".exe"
	build_and_move windows amd64 L2 64 ".exe"
	zip pal_demo.zip {main,test,test_args}{32,64}{,L2}{,.exe}
else
	build "$@"
fi

echo "$PAL_DEMO_DIR/pal_demo.zip"

