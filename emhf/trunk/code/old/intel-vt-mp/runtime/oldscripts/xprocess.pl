#!/usr/bin/perl -w

print `rm TEMPspa_np.c`;

# -P removes annoying source file designators from output
print `gcc -E -P -I ../include/  ./spt_no_pointers.c >| TEMPspa_np.c`;

# New CBMC handles inline assembly
#print `cat spa_npt.c | ./commentInlineASM.pl > spa_np.c`;




