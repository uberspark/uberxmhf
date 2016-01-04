# module to parse object manifest
# author: amit vasudevan (amitvasudevan@acm.org)

package upmf;
use strict;
use warnings;
use Exporter;

our @ISA= qw( Exporter );

# these are exported by default.
our @EXPORT = qw( export_me export_me_too parse_mmap %slab_idtomemoffsets);


our %slab_idtomemoffsets;


sub export_me {
    # stuff
}

sub export_me_too {
    # stuff
}


######
# TODO: move into module
# parses a mmap file and populates relevant global structures
######
sub parse_mmap {
    my($filename, $slabid, $totalslabs) = @_;
    my $i = 0;

    chomp($filename);
    #print "filename:$filename\n";
    tie my @array, 'Tie::File', $filename or die $!;

    #print "parse_mmap: $filename, $slabid...\n";

    while( $i <= $#array) {
        my $line = $array[$i];
        chomp($line);
        $line =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

        my @lineentry = split(/:/, $line);

        $lineentry[0] =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
        $lineentry[1] =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

        $slab_idtomemoffsets{$slabid}{$lineentry[0]} = $lineentry[1];

        $i = $i +1;
    }

    return;
}


1;


