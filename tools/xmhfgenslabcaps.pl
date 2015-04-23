#!/usr/bin/perl
# script to generate slab capabilities for a given slab
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;

parse_gsm($ARGV[0]);

# parses a gsm file and populates relevant
sub parse_gsm {
    my($filename) = @_;
    my $i = 0;

    chomp($filename);
    tie my @array, 'Tie::File', $filename or die $!;


    while( $i <= $#array) {
        my $line = $array[$i];
        chomp($line);
        $line =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

        my @lineentry = split(/:/, $line);

        if($lineentry[0] eq "S"){
            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }elsif( $lineentry[0] eq "U"){

            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }elsif( $lineentry[0] eq "RD"){

            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }elsif( $lineentry[0] eq "RC"){

            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }else{
            #we don't know/care about this line, so just skip it
        }


        $i = $i +1;
    }

}



