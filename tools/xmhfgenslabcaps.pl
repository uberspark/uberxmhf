#!/usr/bin/perl
# script to generate slab capabilities for a given slab
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;
use File::Basename;


# command line inputs
# 0: slabname
# 1: slabid
# 2: rootdir
# 3: SLABS file

my $g_slabname = $ARGV[0];
my $g_slabid = $ARGV[1];
my $g_rootdir = $ARGV[2];
my $g_slabsfile = $ARGV[3];
my $g_totalslabs;

print "slabname:", $g_slabname, "\n";
print "slabid:", $g_slabid, "\n";
print "rootdir:", $g_rootdir, "\n";
print "slabsfile:", $g_slabsfile, "\n";
#print "g_totalslabs:", $g_totalslabs, "\n";


# main loop to iterate through all the slab .gsm's
tie my @array, 'Tie::File', $g_slabsfile or die $!;

my $i = 0;
my $slabdir;
my $slabname;
my $slabgsm;
my $slabtype;

my %slab_idtogsm;
my %slab_idtoname;
my %slab_idtotype;


while( $i <= $#array) {

    my $line = $array[$i];
    chomp($line);

    my $trimline = $line;
    $trimline =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

    # split the line using the comma delimiter
    my @slabinfo = split(/,/, $trimline);

    $slabdir = $g_rootdir.$slabinfo[0];
    $slabdir =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
    $slabname = basename($slabinfo[0]);
    $slabname =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
    $slabtype = $slabinfo[1];
    $slabtype =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
    $slabgsm = $slabdir."/".$slabname.".gsm";

    #print "Slab name: $slabname, gsm:$slabgsm ...\n";
    $slab_idtogsm{$i} = $slabgsm;
    $slab_idtoname{$i} = $slabname;
    $slab_idtotype{$i} = $slabtype;

    #parse_gsm($slabgsm);


    # move on to the next line
    $i = $i + 1;
}

$g_totalslabs = $i;

print "g_totalslabs:", $g_totalslabs, "\n";

$i =0;

while($i < $g_totalslabs){
    print "slabname: $slab_idtoname{$i}, slabgsm: $slab_idtogsm{$i}, slabtype: $slab_idtotype{$i} \n";

    $i=$i+1;
}




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



