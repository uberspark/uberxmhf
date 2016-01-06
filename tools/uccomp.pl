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
my $uapi_key;
my $uapi_fndef;

#while($i < $g_totalslabs){
#    print "slabname: $slab_idtoname{$i}, $slab_idtosubtype{$i} \n";
#
#    $i=$i+1;
#}


%uapi_fnccomppre;
our %uapi_fnccompasserts;


# iterate over the uapi_fndef hashtable
while ( ($uapi_key, $uapi_fndef) = each %uapi_fndef )
{
	# foe ach uapi_key we find, write function definition followed by assertions into check file
	# for each uapi key we find, write function driver code into driver file

        #print "key: $uapi_key, value: $uapi_fndef{$uapi_key}\n";
        print "$uapi_fndef{$uapi_key} { \r\n";
        print "$uapi_fnccomppre{$uapi_key} \r\n";
        print "$uapi_fnccompasserts{$uapi_key} \r\n";
        print "} \r\n\r\n";

}









exit 0;
















