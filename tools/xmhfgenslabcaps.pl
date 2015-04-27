#!/usr/bin/perl
# script to generate slab capabilities for a given slab
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;
use File::Basename;


# command line inputs
# 0: SLABS file with absolute path

my $g_slabsfile = $ARGV[0];
my $g_totalslabs;
my $g_rootdir;

my %slab_idtogsm;
my %slab_idtoname;
my %slab_idtotype;
my %slab_idtouapifnmask;

my %slab_nametocallmask;
my %slab_nametoid;

my $i = 0;
my $slabdir;
my $slabname;
my $slabgsmfile;
my $slabtype;


$g_rootdir = dirname($g_slabsfile)."/";

print "slabsfile:", $g_slabsfile, "\n";
print "rootdir:", $g_rootdir, "\n";




# iterate through all the entries within SLABS file and
# compute total number of slabs while populating global
# slab_idto{gsm,name,type} hashes

tie my @array, 'Tie::File', $g_slabsfile or die $!;

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
    $slabgsm = $slabdir."/".$slabname.".gsm.pp";

    #print "Slab name: $slabname, gsm:$slabgsm ...\n";
    $slab_idtogsm{$i} = $slabgsm;
    $slab_idtoname{$i} = $slabname;
    $slab_idtotype{$i} = $slabtype;
    $slab_nametoid{$slabname} = $i;

    #parse_gsm($slabgsm, $i);

    # move on to the next line
    $i = $i + 1;
}

$g_totalslabs = $i;

print "g_totalslabs:", $g_totalslabs, "\n";

# now iterate through all the slab id's and populate callmask and
# uapimasks

$i =0;

while($i < $g_totalslabs){
    print "slabname: $slab_idtoname{$i}, slabgsm: $slab_idtogsm{$i}, slabtype: $slab_idtotype{$i}, slabcallmask: $slab_nametocallmask{$slab_idtoname{$i}} \n";

    $slab_idtouapifnmask{$i} = parse_gsm($slab_idtogsm{$i}, $i, $g_totalslabs);

    print "uapifnmask:\n";
    print $slab_idtouapifnmask{$i};

    $i=$i+1;
}

######












######
# parses a gsm file and populates relevant global structures
######
sub parse_gsm {
    my($filename, $slabid, $totalslabs) = @_;
    my $i = 0;
    my $j = 0;
    my %slab_idtouapifnmask;
    my $slab_uapifnmaskstring = "";

    chomp($filename);
    tie my @array, 'Tie::File', $filename or die $!;

    print "parse_gsm: $filename, $slabid...\n";

    while( $i <= $#array) {
        my $line = $array[$i];
        chomp($line);
        $line =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

        my @lineentry = split(/:/, $line);

        if($lineentry[0] eq "S"){
            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";
            #lineentry[1] = name of destination slab that this slab calls
            if (exists $slab_nametocallmask{$lineentry[1]}){
                $slab_nametocallmask{$lineentry[1]} |= (1 << $slabid);
            }else {
                $slab_nametocallmask{$lineentry[1]} = (1 << $slabid);
            }

        }elsif( $lineentry[0] eq "U"){
            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";
            #lineentry[1] = destination slab name, lineentry[2] = uapifn
            if (exists $slab_idtouapifnmask{$slab_nametoid{$lineentry[1]}}){
                $slab_idtouapifnmask{$slab_nametoid{$lineentry[1]}} |= (1 << $lineentry[2]);
            }else{
                $slab_idtouapifnmask{$slab_nametoid{$lineentry[1]}} = (1 << $lineentry[2]);
            }

        }elsif( $lineentry[0] eq "RD"){

            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }elsif( $lineentry[0] eq "RC"){

            print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }else{
            #we don't know/care about this line, so just skip it
        }


        $i = $i +1;
    }

    while($j < $totalslabs){
        $slab_uapifnmaskstring = $slab_uapifnmaskstring.sprintf("0x%08x,\n", $slab_idtouapifnmask{$j});
        $j=$j+1;
    }


    return $slab_uapifnmaskstring;

}



