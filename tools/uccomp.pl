#!/usr/bin/perl
# script to generate composition check files
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;
use File::Basename;
use Data::Dumper;

use lib dirname (__FILE__);
use upmf;	#load up the manifest parsing module


# command line inputs
my $g_slabsfile = $ARGV[0];
my $g_memoffsets = $ARGV[1];
my $g_ccompdriverfile = $ARGV[2];
my $g_ccompcheckfile = $ARGV[3];

$g_maxincldevlistentries = $ARGV[4];
$g_maxexcldevlistentries = $ARGV[5];
$g_maxmemoffsetentries = $ARGV[6];


my $g_rootdir;





$g_rootdir = dirname($g_slabsfile)."/";

#print "slabsfile:", $g_slabsfile, "\n";
#print "rootdir:", $g_rootdir, "\n";

print "parsing slab manifests...\n";
upmf_init($g_slabsfile, $g_memoffsets, $g_rootdir);
print "slab manifests parsed\n";



my $i = 0;

while($i < $g_totalslabs){
    print "slabname: $slab_idtoname{$i}, $slab_idtosubtype{$i} \n";

    $i=$i+1;
}









exit 0;
















