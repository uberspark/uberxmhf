#!/bin/bash

if [ -d .svn ] ; then
SVNREV=`svn info | grep Revision | cut -d ' ' -f 2`
else
SVNREV=`git log --max-count=1 | perl -ne 'if (m/@(.*) /) { print "$1\n"; } '`
fi

echo "Detected SVN Revision: $SVNREV"

sudo checkinstall -y --pkgname=trustvisor --pkgversion=0.0.$SVNREV --pkgarch=i386 --pkglicense=Commercial --maintainer=jonmccune@cmu.edu 

#0 -  Maintainer: [ root@mccune ]
#1 -  Summary: [ TrustVisor hypervisor and critical system .h files. ]
#2 -  Name:    [ code ]
#3 -  Version: [  ]
#4 -  Release: [ 1 ]
#5 -  License: [ GPL ]
#6 -  Group:   [ checkinstall ]
#7 -  Architecture: [ i386 ]
#8 -  Source location: [ code ]
#9 -  Alternate source location: [  ]
#10 - Requires: [  ]
#11 - Provides: [ code ]


