#!/bin/sh

EXPORT_PREFIX=doc

# quick and dirty offline documentation generator. Note that to be
# compatible with the dynamically rendered documentation in the
# sourceforge repository viewer, we have to rewrite links to other
# markdown files to point to the generated html files instead.
#
# XXX probably ought to be more selective with the sed find/replace

# generated html files are left in-place. The ideal solution is
# to view these directly, in case links in these refer to other
# resources in the repository.
for f in `find . -name '*.md'`;
do
    DATE=`date`
    cat $f | sed 's/.md/.md.html/g' | pandoc --template=tools/docgen/template/template.html -s -V DATE="`date`" -V SOURCE="$f" -o $f.html

    # copy to EXPORT_PREFIX
    mkdir -p $EXPORT_PREFIX/`dirname $f`
    cp $f.html $EXPORT_PREFIX/`dirname $f`

    # generate index.html from any README.md,
    # and copy to EXPORT_PREFIX
    if [ x`basename $f` = x"README.md" ];
    then
        cp $f.html `dirname $f`/index.html
        cp `dirname $f`/index.html $EXPORT_PREFIX/`dirname $f`
    fi
done
