#!/usr/bin/perl
# generate-hashes.pl
# author(s): amit vasudevan (amitvasudevan@acm.org) 
# this script will generate SHA-1 hashes for 4K pages for PE files
# for a given windows installation

use lib '..';
use File::Find;

find(\&wanted, $ARGV[0]);


sub wanted { 
	# $File::Find::name should have the absolute filename path
	
}

