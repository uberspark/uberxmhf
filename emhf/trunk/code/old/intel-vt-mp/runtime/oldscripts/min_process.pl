#!/usr/bin/perl -w

print `rm TEMPspa_minimal.c`;

# -P removes annoying source file designators from output
print `gcc -E -P -I ../include/  ./minimal_sp.c >| TEMPspa_minimal.c`;

# New CBMC handles inline assembly
#print `cat spa_npt.c | ./commentInlineASM.pl > spa_np.c`;




