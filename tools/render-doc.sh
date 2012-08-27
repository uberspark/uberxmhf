#!/bin/sh

# quick and dirty offline documentation generator. Note that to be
# compatible with the dynamically rendered documentation in the
# sourceforge repository viewer, we have to rewrite links to other
# markdown files to point to the generated html files instead.
#
# XXX probably ought to be more selective with the sed find/replace

for f in `find . -name '*.md'`;
do
    cat $f | sed 's/.md/.md.html/g' | pandoc -s -o $f.html;
done
