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
# if [ $# -ne 2  ]
# then
#        echo "Usage: dorelease.sh <release number> <changelog file>"
#        exit
# fi

# XMHFRELEASE=v$1
# CHANGELOGFILE=$2

# check for correct command line parameters, else bail out with
# an usage banner
if [ $# -ne 1  ]
then
        echo "Usage: dorelease.sh <release number>"
        exit
fi

XMHFRELEASENUM=$1
XMHFRELEASE=v$1
CHANGELOGFILE="CHANGELOG.md"
XMHFRELEASENAME="xmhf-$XMHFRELEASENUM"
XMHFRELEASETMPDIR="/tmp/xmhfrelease"


echo -------------------------------------------------------------------
echo Preparing XMHF release: $XMHFRELEASE
echo Using Changelog file: $CHANGELOGFILE
echo -------------------------------------------------------------------

# check if we can stat the changelog file, if not bail out
if [ ! -f $CHANGELOGFILE ]; then
	echo "Could not find/stat changelog file: $CHANGELOGFILE"
	echo "Are you forgetting to run the release script rom the XMHF git repo root?"
	exit
fi

# check if we are on the "master" branch, if not bail out
XMHFBRANCHNAME=`git rev-parse --abbrev-ref HEAD`
# if [ $XMHFBRANCHNAME != "master" ]; then
#	echo "Release can only be done on the master branch."
#	echo "Current branch: $XMHFBRANCHNAME"
#	exit
# fi

# check if the branch is dirty (uncommitted changes) and if so bail
# out with a warning
#IS_DIRTY=`git status --porcelain | perl -n -e 'if ($_ !~ /^\?\?/) { print "DIRTY\n"; exit; }'`
#if [ "$IS_DIRTY" == "DIRTY" ]; then
#    echo "Branch dirty. Did you forget to commit something?" >&2
#    exit 1
#fi

# barf out the CHANGELOG so we are happy with its content before 
# proceeding
echo CHANGELOG.md...
cat $CHANGELOGFILE
echo -------------------------------------------------------------------


# no return after this point, so make absolutely sure we are good with
# making the release

while true; do
    read -p "Do you wish to continue with the release (yes/no)?" yn
    case $yn in
        [Yy][eE][sS] ) break;;
        [Nn]* ) exit;;
        * ) echo "Please answer yes or no.";;
    esac
done

echo
echo Proceeding with release $XMHFRELEASE...
echo

# cleanup the branch of untracked files
echo Proceeding to cleanup up untracked files on branch $XMHFBRANCHNAME ...
git clean -fdx
echo Cleaned up untracked files.

# make temporary release folder
echo Proceeding to make temporary release folder $XMHFRELEASETMPDIR...
rm -rf $XMHFRELEASETMPDIR
mkdir -p $XMHFRELEASETMPDIR
echo Temporary release folder created.

# implant release version and prepare for release build
echo Proceeding to implant release version information...
	# check if we can stat Makefile.in within XMHF core, if not bail out
	if [ ! -f ./xmhf/Makefile.in ]; then
		echo "Could not find/stat XMHF core Makefile.in"
		echo "Are you forgetting to run the release script rom the XMHF git repo root?"
		exit
	fi

	# customize Makefile.in with the release details
	sed '/export XMHF_BUILD_VERSION/c export XMHF_BUILD_VERSION := '"$XMHFRELEASE"'' ./xmhf/Makefile.in >$XMHFRELEASETMPDIR/Makefile.in.release0
	sed '/export XMHF_BUILD_REVISION_BRANCH/c export XMHF_BUILD_REVISION_BRANCH := '"$XMHFBRANCHNAME"'' $XMHFRELEASETMPDIR/Makefile.in.release0 >$XMHFRELEASETMPDIR/Makefile.in.release1
	sed '/export XMHF_BUILD_REVISION_COMMIT/c export XMHF_BUILD_REVISION_COMMIT := release' $XMHFRELEASETMPDIR/Makefile.in.release1 >$XMHFRELEASETMPDIR/Makefile.in.release
	cp -f $XMHFRELEASETMPDIR/Makefile.in.release ./xmhf/Makefile.in
	rm -rf $XMHFRELEASETMPDIR/Makefile.in.*
echo Release version information embedded.

# make a tarball for the release 
echo Proceeding to build release tarball $XMHFRELEASENAME.tar.gz...
rm -rf $XMHFRELEASETMPDIR
mkdir -p $XMHFRELEASETMPDIR
git archive --prefix=$XMHFRELEASENAME/ --format=tar HEAD | gzip >$XMHFRELEASETMPDIR/$XMHFRELEASENAME.tar.gz
echo Built $XMHFRELEASENAME.tar.gz


