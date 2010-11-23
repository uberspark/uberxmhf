#!/usr/bin/perl -w

print `rm TEMPspa.c`;

# -P removes annoying source file designators from output
print `gcc -E -P -I ../include/  ./shadow_paging_npae.c >| TEMPspa.c`;

# New CBMC handles inline assembly
#print `cat spa_t.c | ./commentInlineASM.pl > spa.c`;

#print `rm spa_t.c `;
