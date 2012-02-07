#!/bin/bash

perl -pe  's/\e\[[\d,;\s]*[a-zA-Z]//g; s/\e\][\d];//g; s/\r\n/\n/g; s/[\000-\011]//g; s/[\013-\037]//g'

# Thanks: http://www.perlmonks.org/?node_id=132997
# perl -pe  's/\e\[[\d,\s]*[a-zA-Z]//g; s/\e\][\d];//g; s/\r\n/\n/g; s/[+\000-\011]//g; s/[\013-\037]//g' < in > out
