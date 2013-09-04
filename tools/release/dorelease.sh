#!/bin/bash

# dorelease.sh
# helper script to handle all the (mundane) steps required for a
# release

# author: amit vasudevan (amitvasudevan@acm.org)

# Immediately bail out if any errors are detected (non-zero exit
# status from a child process)
set -e

# check for exactly two command line parameters, else bail out with
# an usage banner
if [ $# -ne 2  ]
then
        echo "Usage: dorelease.sh <release number> <changelog file>"
        exit
fi

XMHFRELEASE=v$1
CHANGELOGFILE=$2

echo -------------------------------------------------------------------
echo Preparing XMHF release: $XMHFRELEASE
echo Using Changelog file: $CHANGELOGFILE
echo -------------------------------------------------------------------

# check if we can stat the changelog file, if not bail out
if [ ! -f $CHANGELOGFILE ]; then
	echo "Could not find/stat changelog file: $CHANGELOGFILE"
	exit
fi

