#!/usr/bin/perl -w

print `rm spa.c spa_t.c`;

# Define __SP__ to get proprocessor to include conditional #defines
# -P removes annoying source file designators from output
print `gcc -E -P -I ../include/  ./shadow_paging_npae.c >| spa_t.c`;

print `cat spa_t.c | ./commentInlineASM.pl > spa.c`;

