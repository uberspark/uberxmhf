#!/usr/bin/perl
# generate-ldnpb.pl
# author(s): amit vasudevan (amitvasudevan@acm.org) 
# this script will generate Lockdown parameter block for the 
# trusted environment (TE) which includes the TE signature and full and
# partial code page hashes

use bignum qw/hex/;

if ($#ARGV != 1 ) {
	print "usage: generate-ldnpb.pl full_hashlist partial_hashlist\n";
	exit;
}

$full_hashlist=$ARGV[0];
$partial_hashlist=$ARGV[1];

print "full hash list file: $full_hashlist\n";
print "partial hash list file: $partial_hashlist\n";

$ldnpbfilename = "ldnpb_te.bin";

open LDNPBBIN, ">", $ldnpbfilename
or die "\nCan't open $ldnpbfilename for writing: $!\n";
binmode( LDNPBBIN );



# open full hashlist file and iterate through all the hashes there
$full_hashlist_totalelements = 0;

open FHASHFULL, $full_hashlist
or die "\nCan't open $full_hashlist for reading: $!\n";


while(<FHASHFULL>)
{
	my($line) = $_;

	#strip the trailing from the line
	chomp($line);
	
	#skip empty lines
	if($line ne ""){
		 # Print the line to the screen and add a newline
		print "$line\n";
		my $output = pack( "N", hex($line));
		print( LDNPBBIN $output );
	}
 }

close FHASHFULL
or die "Can't close $full_hashlist: $!\n";


close LDNPBBIN
or die "Can't close $ldnpbfilename: $!\n";
