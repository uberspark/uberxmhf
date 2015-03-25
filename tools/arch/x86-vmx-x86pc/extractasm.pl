#!/usr/bin/perl
# script to extract asm instruction from compcert annotations
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;

chomp(my $filename = $ARGV[0]);
tie my @array, 'Tie::File', $filename or die $!;

my $i = 0;

while( $i <= $#array) {
    my $line = $array[$i];
    chomp($line);

    my $trimline = $line;
    $trimline =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

    #print "Processing line: $line \n";

    # check if line is an annotation
	if( $trimline =~ /^annot/ ){
        #print "Got annot line\n";
        my $insn = substr($trimline, 7, -3);
        print "$insn\n";
    }

    # move on to the next line
    $i = $i + 1;
}
