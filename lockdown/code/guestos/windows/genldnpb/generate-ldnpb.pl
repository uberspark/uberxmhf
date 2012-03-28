#!/usr/bin/perl
# generate-ldnpb.pl
# author(s): amit vasudevan (amitvasudevan@acm.org) 
# this script will generate Lockdown parameter block for the 
# trusted environment (TE) which includes the TE signature and full and
# partial code page hashes

if ($#ARGV != 1 ) {
	print "usage: generate-ldnpb.pl full_hashlist partial_hashlist\n";
	exit;
}

$full_hashlist=$ARGV[0];
$partial_hashlist=$ARGV[1];

print "full hash list file: $full_hashlist\n";
print "partial hash list file: $partial_hashlist\n";
