#!/usr/bin/perl

#/*
# * @XMHF_LICENSE_HEADER_START@
# *
# * eXtensible, Modular Hypervisor Framework (XMHF)
# * Copyright (c) 2009-2012 Carnegie Mellon University
# * Copyright (c) 2010-2012 VDG Inc.
# * All Rights Reserved.
# *
# * Developed by: XMHF Team
# *               Carnegie Mellon University / CyLab
# *               VDG Inc.
# *               http://xmhf.org
# *
# * Redistribution and use in source and binary forms, with or without
# * modification, are permitted provided that the following conditions
# * are met:
# *
# * Redistributions of source code must retain the above copyright
# * notice, this list of conditions and the following disclaimer.
# *
# * Redistributions in binary form must reproduce the above copyright
# * notice, this list of conditions and the following disclaimer in
# * the documentation and/or other materials provided with the
# * distribution.
# *
# * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
# * its contributors may be used to endorse or promote products derived
# * from this software without specific prior written permission.
# *
# * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
# * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
# * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
# * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
# * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
# * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
# * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
# * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
# * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# * SUCH DAMAGE.
# *
# * @XMHF_LICENSE_HEADER_END@
# */

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
