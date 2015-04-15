#!/bin/sh
#autoreconf --install
#automake --add-missing --copy >/dev/null 2>&1

autoconf
autoconf --output=configure_slab configure_slab.ac

exit 0
