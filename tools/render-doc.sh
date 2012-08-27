#!/bin/sh

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
    cat $f | sed 's/.md/.md.html/g' | pandoc -s -o $f.html;
    if [ x`basename $f` = x"README.md" ]; then cp $f.html `dirname $f`/index.html; fi
done

# copy just the generated html files to another directory.
# Links to other resources in the repo will be broken, but
# this can be easily hosted or distributed.
find . \( -name '*.md.html' -o -name index.html \) -exec rsync -R \{\} xmhf-doc/ \;
