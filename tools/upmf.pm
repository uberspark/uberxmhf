# module to parse object manifest
# author: amit vasudevan (amitvasudevan@acm.org)

package upmf;
use strict;
#use warnings;
use Exporter;

our @ISA= qw( Exporter );

# these are exported by default.
our @EXPORT = qw( export_me export_me_too parse_gsm parse_mmap %slab_idtomemoffsets %slab_idtomemoffsetstring %slab_idtocallmask %slab_nametoid %slab_idtoname $g_maxincldevlistentries $g_maxexcldevlistentries %slab_idtomemgrantreadcaps %slab_idtomemgrantwritecaps %slab_idtodatasize %slab_idtocodesize %slab_idtostacksize %slab_idtodmadatasize $g_maxmemoffsetentries %slab_idtordinclentries %slab_idtordinclcount %slab_idtordexclentries %slab_idtordexclcount);


our %slab_idtomemoffsets;
our %slab_idtomemoffsetstring;
our %slab_idtocallmask;
our %slab_nametoid;
our %slab_idtoname;
our %slab_idtomemgrantreadcaps;
our %slab_idtomemgrantwritecaps;
our %slab_idtodatasize;
our %slab_idtocodesize;
our %slab_idtostacksize;
our %slab_idtodmadatasize;
our %slab_idtordinclentries;
our %slab_idtordinclcount;
our %slab_idtordexclentries;
our %slab_idtordexclcount;



our $g_maxincldevlistentries;
our $g_maxexcldevlistentries;
our $g_maxmemoffsetentries;


sub export_me {
    # stuff
}

sub export_me_too {
    # stuff
}



######
# TODO: move into module
# parses a gsm file and populates relevant global structures
######
sub parse_gsm {
    my($filename, $slabid, $totalslabs, $is_memoffsets) = @_;
    my $i = 0;
    my $j = 0;
    my $slab_rdinclcount=0;
    my $slab_rdexclcount=0;
    my $slab_rdinclentriesstring="";
    my $slab_rdexclentriesstring="";
    my %slab_idtouapifnmask;
    my $slab_uapifnmaskstring = "";
    my $slab_memoffsetsstring = "";
    my $slab_memoffsetcount=0;

    chomp($filename);
    tie my @array, 'Tie::File', $filename or die $!;

    #print "parse_gsm: $filename, $slabid, $is_memoffsets...\n";

    $slab_rdinclentriesstring = $slab_rdinclentriesstring."{ \n";
    $slab_rdexclentriesstring = $slab_rdexclentriesstring."{ \n";

    while( $i <= $#array) {
        my $line = $array[$i];
        chomp($line);
        $line =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

        my @lineentry = split(/:/, $line);

        if($lineentry[0] eq "S"){
            #print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";
            #lineentry[1] = name of destination slab that this slab calls
            if (exists $slab_idtocallmask{$slab_nametoid{$lineentry[1]}}){
                $slab_idtocallmask{$slab_nametoid{$lineentry[1]}} |= (1 << $slabid);
            }else {
                $slab_idtocallmask{$slab_nametoid{$lineentry[1]}} = (1 << $slabid);
            }

        }elsif( $lineentry[0] eq "U"){
            #print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";
            #lineentry[1] = destination slab name, lineentry[2] = uapifn
            if (exists $slab_idtouapifnmask{$slab_nametoid{$lineentry[1]}}){
                $slab_idtouapifnmask{$slab_nametoid{$lineentry[1]}} |= (1 << $lineentry[2]);
            }else{
                $slab_idtouapifnmask{$slab_nametoid{$lineentry[1]}} = (1 << $lineentry[2]);
            }

        }elsif( $lineentry[0] eq "RD"){
            #print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";
            #lineentry[1]=INCL or EXCL, lineentry[2] = vendor_id, lineentry[3] = device_id
            if ( $lineentry[1] eq "INCL"){
                if($slab_rdinclcount >= $g_maxincldevlistentries){
                    print "\nError: Too many RD INCL entries (max=$g_maxincldevlistentries)!";
                    exit 1;
                }
                $slab_rdinclentriesstring = $slab_rdinclentriesstring."\t{ .vendor_id= ".$lineentry[2].", .device_id= ".$lineentry[3]." },\n";
                $slab_rdinclcount = $slab_rdinclcount + 1;
            } elsif ( $lineentry[1] eq "EXCL"){
                if($slab_rdexclcount >= $g_maxexcldevlistentries){
                    print "\nError: Too many RD EXCL entries (max=$g_maxexcldevlistentries)!";
                    exit 1;
                }
                $slab_rdexclentriesstring = $slab_rdexclentriesstring."\t{ .vendor_id= ".$lineentry[2].", .device_id= ".$lineentry[3]." },\n";
                $slab_rdexclcount = $slab_rdexclcount + 1;
            }else {
                print "\nError: Illegal RD entry qualifier ($lineentry[1])!";
                exit 1;
            }

        }elsif( $lineentry[0] eq "RM"){
            #print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";
            #lineentry[1]=READ or WRITE, lineentry[2] = slabname
            if ( $lineentry[1] eq "READ"){

                if (exists $slab_idtomemgrantreadcaps{$slabid}){
                    $slab_idtomemgrantreadcaps{$slabid} |= (1 << $slab_nametoid{$lineentry[2]});
                }else{
                    $slab_idtomemgrantreadcaps{$slabid} = (1 << $slab_nametoid{$lineentry[2]});
                }


            } elsif ( $lineentry[1] eq "WRITE"){

                if (exists $slab_idtomemgrantwritecaps{$slabid}){
                    $slab_idtomemgrantwritecaps{$slabid} |= (1 << $slab_nametoid{$lineentry[2]});
                }else{
                    $slab_idtomemgrantwritecaps{$slabid} = (1 << $slab_nametoid{$lineentry[2]});
                }

            }else {
                print "\nError: Illegal RM entry qualifier ($lineentry[1])!";
                exit 1;
            }


        }elsif( $lineentry[0] eq "RC"){

            #print $lineentry[0], $lineentry[1], $lineentry[2], $lineentry[3], $lineentry[4], "\n";

        }elsif( $lineentry[0] eq "MS"){
            #$lineentry[1]=DATA,CODE,STACK,DMADATA, $lineentry[2] = size in bytes
            if ( $lineentry[1] eq "DATA"){
                $slab_idtodatasize{$slabid} = $lineentry[2];
            } elsif ( $lineentry[1] eq "CODE"){
                $slab_idtocodesize{$slabid} = $lineentry[2];
            } elsif ( $lineentry[1] eq "STACK"){
                $slab_idtostacksize{$slabid} = $lineentry[2];
            } elsif ( $lineentry[1] eq "DMADATA"){
                $slab_idtodmadatasize{$slabid} = $lineentry[2];
            }else {
                print "\nError: Illegal MS entry qualifier ($lineentry[1])!";
                exit 1;
            }


        }elsif( $lineentry[0] eq "EX"){
            #$lineentry[1]=export variable name
            $lineentry[1] =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

            #if we are processing memoffsets, then lookup this variable address
            if($is_memoffsets == 1){
                if(exists $slab_idtomemoffsets{$slabid}{$lineentry[1]}){
                    if($slab_memoffsetcount < $g_maxmemoffsetentries) {
                        $slab_memoffsetsstring = $slab_memoffsetsstring."\t0x".$slab_idtomemoffsets{$slabid}{$lineentry[1]}.",\n";
                        $slab_memoffsetcount += 1;
                    }else{
                        print "\nError: Max. EX entries exceeded!";
                        exit 1;
                    }
                }else{
                    print "\nError: No entry found for slab: $slab_idtoname{$i}, EX entry: $lineentry[1]!";
                    exit 1;
                }
            }


        }else{
            #we don't know/care about this line, so just skip it
        }


        $i = $i +1;
    }

    if($slab_rdinclcount == 0){
        $slab_rdinclentriesstring = $slab_rdinclentriesstring."0 \n}, \n";
    }else{
        $slab_rdinclentriesstring = $slab_rdinclentriesstring."}, \n";
    }
    if($slab_rdexclcount == 0){
        $slab_rdexclentriesstring = $slab_rdexclentriesstring."0 \n}, \n";
    }else{
        $slab_rdexclentriesstring = $slab_rdexclentriesstring."}, \n";
    }

    $slab_idtordinclentries{$slabid} = $slab_rdinclentriesstring;
    $slab_idtordexclentries{$slabid} = $slab_rdexclentriesstring;
    $slab_idtordinclcount{$slabid} = $slab_rdinclcount;
    $slab_idtordexclcount{$slabid} = $slab_rdexclcount;

    while($j < $totalslabs){
        $slab_uapifnmaskstring = $slab_uapifnmaskstring.sprintf("\t0x%08x,\n", $slab_idtouapifnmask{$j});
        $j=$j+1;
    }


    #if we are processing memoffsets, then store memoffsets string indexed by slabid
    if($is_memoffsets == 1){
        if($slab_memoffsetsstring eq ""){
            $slab_idtomemoffsetstring{$slabid} = "0";
        }else{
            $slab_idtomemoffsetstring{$slabid} = $slab_memoffsetsstring;
        }
    }

    return $slab_uapifnmaskstring;

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


