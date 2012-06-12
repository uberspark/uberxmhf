#!/usr/bin/perl
# generate-ldnpb.pl
# author(s): amit vasudevan (amitvasudevan@acm.org) 
# this script will generate Lockdown parameter block for the 
# trusted environment (TE) which includes the TE signature and full and
# partial code page hashes

use lib '..';
use bignum;

# if we are called with insufficient command line parameters, say
# what we should be called with
if ($#ARGV != 1 ) {
	print "usage: generate-ldnpb.pl full_hashlist partial_hashlist\n";
	exit;
}

# grab the full and partial hash list file names
$full_hashlist=$ARGV[0];
$partial_hashlist=$ARGV[1];

# get the total number of full and partial code page hashes
# we just use wc for this
$full_hashlist_count = `wc -l < $full_hashlist`;
die "wc failed: $?" if $?;
chomp($full_hashlist_count);

$partial_hashlist_count = `wc -l < $partial_hashlist`;
die "wc failed: $?" if $?;
chomp($partial_hashlist_count);

# dump out some info on the full and partial hash list files
print "full hash list file: $full_hashlist, $full_hashlist_count hashes\n";
print "partial hash list file: $partial_hashlist, $partial_hashlist_count hashes\n";

# our TE parameter block binary blob file name
$ldnpbfilename = "ldnpb_te.bin";

# open our TE parameter block file
open LDNPBBIN, ">", $ldnpbfilename
or die "\nCan't open $ldnpbfilename for writing: $!\n";

# switch to binary mode
binmode( LDNPBBIN );

# write the TE parameter block header TRUE
print( LDNPBBIN "TRUE");

# write the full and partial hash list element counts
print( LDNPBBIN pack( "L", $full_hashlist_count) );
print( LDNPBBIN pack( "L", $partial_hashlist_count) );

# open full hash list file and iterate through all the hashes there
# writing them out as a 160-bit value to the TE parameter block blob
open FHASHFULL, $full_hashlist
or die "\nCan't open $full_hashlist for reading: $!\n";

while(<FHASHFULL>)
{
	my($line) = $_;

	#strip the trailing from the line
	chomp($line);
	
	#skip empty lines
	if($line ne ""){
		@info=split(/:/, $line);
		
		$hashinfo_pageoffset= hex($info[0]);
		$hashinfo_size = hex($info[1]);
		$hashinfo_shanum = $info[2];

		# 32-bit page offset and size fields
		print( LDNPBBIN pack( "L", $hashinfo_pageoffset) );
		print( LDNPBBIN pack( "L", $hashinfo_size) );

		# 160-bit hash = 20 bytes = 40 hex characters
		# input $line is little endian
        my $output = pack( "H40", $hashinfo_shanum);
		print( LDNPBBIN $output );
	}
}

close FHASHFULL
or die "Can't close $full_hashlist: $!\n";


# open partial hash list file and iterate through all the hashes there
# writing them out as a 160-bit value to the TE parameter block blob
open FHASHPART, $partial_hashlist
or die "\nCan't open $partial_hashlist for reading: $!\n";

while(<FHASHPART>)
{
	my($line) = $_;

	#strip the trailing from the line
	chomp($line);
	
	#skip empty lines
	if($line ne ""){
		@info=split(/:/, $line);
		
		$hashinfo_pageoffset= hex($info[0]);
		$hashinfo_size = hex($info[1]);
		$hashinfo_shanum = $info[2];

		# 32-bit page offset and size fields
		print( LDNPBBIN pack( "L", $hashinfo_pageoffset) );
		print( LDNPBBIN pack( "L", $hashinfo_size) );

		# 160-bit hash = 20 bytes = 40 hex characters
		# input $line is little endian
        my $output = pack( "H40", $line);
		print( LDNPBBIN $output );
	}
}

close FHASHPART
or die "Can't close $partial_hashlist: $!\n";

close LDNPBBIN
or die "Can't close $ldnpbfilename: $!\n";
