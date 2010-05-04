#!/usr/bin/env perl

#
#  $Id: size_to_csv.pl 1 2008-04-12 19:52:33Z jcw $
#  $Revision: 1 $
#  $Author: jcw $
#  $Date: 2008-04-12 15:52:33 -0400 (Sat, 12 Apr 2008) $
#  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/size_to_csv.pl $
#

use strict;
use warnings;

#
#  Set to non-0 to keep columns that are not .comment or .debug*
#
my $useful_columns_only = 0;

my @ignore = qw(
	.comment
	.debug.*
);

my @ordered_columns = qw(
	.text
	.data
	.rodata
	.rodata.str1.4
	.bss 
);

my($file, %entries, %keys);

@ignore = () if (!$useful_columns_only);
my $ignore = join '|', @ignore;
my $state = 'SKIPPING';
while (<>) {
	if ($state eq 'SKIPPING') {
		/:$/ or next;
		($file) = split /\s+/;
		$entries{$file} = {};
		$state = 'HEADER';
	}
	elsif ($state eq 'HEADER') {
		/^section/ or die "Error: next line is not header\n";
		$state = 'READING';
	}
	elsif ($state eq 'READING' ) {
		if (/^Total/) {
			$state = 'SKIPPING';
		}
		elsif (/^\.\w+/) {
			my ($section, $value) = split /\s+/;
			next if $section =~ /^($ignore)$/;
			$keys{$section} = 1;
			$entries{$file}{$section} = $value;
		}
	}
}

delete $keys{$_} for @ordered_columns;
my @keys = (@ordered_columns, sort keys %keys);
my @arr  = ['file', @keys];
for $file (sort keys %entries) {
	push @arr, [ $file, map { $entries{$file}{$_} || 0 } @keys ]
}
for(@arr) { print join(",", @$_), "\n" }
