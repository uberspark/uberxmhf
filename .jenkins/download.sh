#!/bin/bash

set -xe
if [ $# -le 0 ]; then
	echo "Error: no enough arguments"; exit 1
fi

DOWNLOAD_DIR="$1"
mkdir -p "$DOWNLOAD_DIR"
shift

download () {
	TARGET_FILE="$DOWNLOAD_DIR/$2"
	if [ -f "$TARGET_FILE" ]; then
		echo "$TARGET_FILE already exists"
	else
		if ! python3 -c 'import gdown'; then
			python3 -m pip install gdown
		fi
		python3 -m gdown.cli "$1" -O "$TARGET_FILE"
	fi
}

while [ "$#" -gt 0 ]; do
	case "$1" in
		debian11x86.qcow2)
			download "1T1Yw8cBa2zo1fWSZIkry0aOuz2pZS6Tl" "$1"
			;;
		debian11x64.qcow2)
			download "1WntdHCKNmuJ5I34xqriokMlSAC3KcqL-" "$1"
			;;
		*)
			echo "Error: unknown file $1"; exit 1
			;;
	esac
	shift 
done

