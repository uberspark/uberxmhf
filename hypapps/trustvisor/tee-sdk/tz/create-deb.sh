#!/bin/bash

if [ -d .svn ] ; then
SVNREV=`svn info | grep Revision | cut -d ' ' -f 2`
else
SVNREV=`git log --max-count=1 | perl -ne 'if (m/@(.*) /) { print "$1\n"; } '`
fi

echo "Detected SVN Revision: $SVNREV"

debuild -us -uc -b

