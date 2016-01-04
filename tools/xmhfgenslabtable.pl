#!/usr/bin/perl
# script to generate XMHF slab physical memory extents
# based on the slab names provided
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;
use File::Basename;
use Data::Dumper;

use lib dirname (__FILE__);
use upmf;	#load up the manifest parsing module


# command line inputs

my $g_slabsfile = $ARGV[0];
my $g_outputfile_slabinfotable = $ARGV[1];
my $g_outputfile_linkerscript = $ARGV[2];
my $g_loadaddr = $ARGV[3];
my $g_loadmaxsize = $ARGV[4];
my $g_totaluhslabs = $ARGV[5];
my $g_memoffsets = $ARGV[9];

$g_maxincldevlistentries = $ARGV[6];
$g_maxexcldevlistentries = $ARGV[7];
$g_maxmemoffsetentries = $ARGV[8];



my $g_totalslabmempgtblsets;
my $g_totalslabiotblsets;
my $g_uhslabcounter;
my $g_ugslabcounter;


my $g_totalslabs;
my $g_rootdir;

my %slab_idtogsm;
my %slab_idtommapfile;
my %slab_idtodir;
my %slab_idtotype;
my %slab_idtosubtype;
my %slab_idtouapifnmask;






my %slab_idtodata_addrstart;
my %slab_idtodata_addrend;
my %slab_idtocode_addrstart;
my %slab_idtocode_addrend;
my %slab_idtostack_addrstart;
my %slab_idtostack_addrend;
my %slab_idtodmadata_addrstart;
my %slab_idtodmadata_addrend;




my $i = 0;
my $slabdir;
my $slabname;
my $slabgsmfile;
my $slabtype;
my $slabsubtype;
my $slabmmapfile;

my $g_memmapaddr=0;


my $fh;








$g_rootdir = dirname($g_slabsfile)."/";

$g_totaluhslabmempgtblsets = $g_totaluhslabs;
$g_totaluvslabiotblsets = $g_totaluhslabs;
$g_totalslabmempgtblsets = $g_totaluhslabmempgtblsets + 2;
$g_totalslabiotblsets = $g_totaluvslabiotblsets + 2;

$g_uhslabcounter = 0;
$g_ugslabcounter = 0;


#print "slabsfile:", $g_slabsfile, "\n";
#print "rootdir:", $g_rootdir, "\n";


# TODO: move into module [START]

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
    $slabsubtype = $slabinfo[2];
    $slabsubtype =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
    $slabgsm = $slabdir."/".$slabname.".gsm.pp";
    $slabmmapfile = $g_rootdir."_objects/_objs_slab_".$slabname."/".$slabname.".mmap";

    #print "Slab name: $slabname, mmap:$slabmmapfile ...\n";
    $slab_idtodir{$i} = $slabdir;
    $slab_idtogsm{$i} = $slabgsm;
    $slab_idtommapfile{$i} = $slabmmapfile;
    $slab_idtoname{$i} = $slabname;
    $slab_idtotype{$i} = $slabtype;
    $slab_idtosubtype{$i} = $slabsubtype;
    $slab_nametoid{$slabname} = $i;

    # move on to the next line
    $i = $i + 1;
}

$g_totalslabs = $i;

print "g_totalslabs:", $g_totalslabs, "\n";

# now iterate through all the slab id's and populate callmask and
# uapimasks

$i =0;
while($i < $g_totalslabs){
    #print "slabname: $slab_idtoname{$i}, slabgsm: $slab_idtogsm{$i}, slabtype: $slab_idtotype{$i}, slabcallmask: $slab_idtocallmask{$i} \n";
    if($g_memoffsets eq "MEMOFFSETS"){
        parse_mmap($slab_idtommapfile{$i}, $i, $g_totalslabs);
        $slab_idtouapifnmask{$i} = parse_gsm($slab_idtogsm{$i}, $i, $g_totalslabs, 1);
    }else{
        $slab_idtouapifnmask{$i} = parse_gsm($slab_idtogsm{$i}, $i, $g_totalslabs, 0);
    }
    #print "uapifnmask:\n";
    #print $slab_idtouapifnmask{$i};
    $i=$i+1;
}

######

# TODO: move into module [END]






print "Proceeding to compute memory map...\n";


######
# compute memory map
######
$i =0;
$g_memmapaddr = hex $g_loadaddr;
while($i < $g_totalslabs){
    #print "slabname: $slab_idtoname{$i}, code: $slab_idtocodesize{$i}, data: $slab_idtodatasize{$i}, stack: $slab_idtostacksize{$i}, dmadata: $slab_idtodmadatasize{$i} \n";
    $slab_idtocode_addrstart{$i} = sprintf("0x%08x", $g_memmapaddr);
    $g_memmapaddr += hex $slab_idtocodesize{$i};
    $slab_idtocode_addrend{$i} = sprintf("0x%08x", $g_memmapaddr);

    $slab_idtodata_addrstart{$i} = sprintf("0x%08x", $g_memmapaddr);
    $g_memmapaddr += hex $slab_idtodatasize{$i};
    $slab_idtodata_addrend{$i} = sprintf("0x%08x", $g_memmapaddr);

    $slab_idtostack_addrstart{$i} = sprintf("0x%08x", $g_memmapaddr);
    $g_memmapaddr += hex $slab_idtostacksize{$i};
    $slab_idtostack_addrend{$i} = sprintf("0x%08x", $g_memmapaddr);

    $slab_idtodmadata_addrstart{$i} = sprintf("0x%08x", $g_memmapaddr);
    $g_memmapaddr += hex $slab_idtodmadatasize{$i};
    $slab_idtodmadata_addrend{$i} = sprintf("0x%08x", $g_memmapaddr);

    $i=$i+1;
}

print "Computed memory map\n";


#$i =0;
#while($i < $g_totalslabs){
#    print "slabname: $slab_idtoname{$i} \n";
#    printf("code    - addrstart= %x, addrend=%x \n", $slab_idtocode_addrstart{$i}, $slab_idtocode_addrend{$i});
#    printf("data    - addrstart= %x, addrend=%x \n", $slab_idtodata_addrstart{$i}, $slab_idtodata_addrend{$i});
#    printf("stack   - addrstart= %x, addrend=%x \n", $slab_idtostack_addrstart{$i}, $slab_idtostack_addrend{$i});
#    printf("dmadata - addrstart= %x, addrend=%x \n", $slab_idtodmadata_addrstart{$i}, $slab_idtodmadata_addrend{$i});
#
#
#    $i=$i+1;
#}

#exit 0;



######
# debug
######

#print Dumper(\%slab_idtomemoffsets); # much better


#$i =0;
#while($i < $g_totalslabs){
#    print "slab:$slab_idtoname{$i} exports\n";
#    print "$slab_idtomemoffsetstring{$i} \n";
#    $i = $i + 1;
#}

#exit 0;






######
# configure the slabs
######

if($g_memoffsets eq "MEMOFFSETS"){
    #no configuration needed when doing real build
}else{

    $i =0;
    while($i < $g_totalslabs){
        #print "Configuring slab: $slab_idtodir{$i} with type:$slab_idtotype{$i}:$slab_idtosubtype{$i} ...\n";
        system "cd $slab_idtodir{$i} && ../../configure_slab "
                . " --with-slabtype=$slab_idtotype{$i}"
                . " --with-slabsubtype=$slab_idtosubtype{$i}"
                . " --with-slabcodestart=$slab_idtocode_addrstart{$i}"
                . " --with-slabcodeend=$slab_idtocode_addrend{$i}"
                . " --with-slabdatastart=$slab_idtodata_addrstart{$i}"
                . " --with-slabdataend=$slab_idtodata_addrend{$i}"
                . " --with-slabstackstart=$slab_idtostack_addrstart{$i}"
                . " --with-slabstackend=$slab_idtostack_addrend{$i}"
                . " --with-slabdmadatastart=$slab_idtodmadata_addrstart{$i}"
                . " --with-slabdmadataend=$slab_idtodmadata_addrend{$i}"
                . " >/dev/null 2>&1";

        $i = $i + 1;
    }

}

print "Configured slabs\n";








######
# output slab info table
######

open($fh, '>', $g_outputfile_slabinfotable) or die "Could not open file '$g_outputfile_slabinfotable' $!";

print $fh "\n/* autogenerated XMHF/GEEC sentinel slab info table */";
print $fh "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";

print $fh "\n";

#$i=0;
#while( $i < $g_totalslabs) {
#	print $fh "\n";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_code_start[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_code_end[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_data_start[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_data_end[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_stack_start[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_stack_end[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_dmadata_start[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_dmadata_end[];";
#	print $fh "\nextern u8 _slab_$slab_idtoname{$i}_entrypoint[];";
#
#	$i++;
#}

print $fh "\n";
print $fh "\n__attribute__(( section(\".data\") )) __attribute__((aligned(4096))) xmhfgeec_slab_info_t xmhfgeec_slab_info_table[] = {";


$i = 0;
while( $i < $g_totalslabs ){
	#print "Writing up for $i...\n";

	print $fh "\n";
    print $fh "\n	//$slab_idtoname{$i}";
    print $fh "\n	{";

    #slab_inuse
    print $fh "\n	    true,";

    #slab_type
    if($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "PRIME"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "SENTINEL"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_SENTINEL,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "INIT"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "XCORE"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "XHYPAPP"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "UAPI"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "EXCEPTION"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "INTERCEPT"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slab_idtotype{$i} eq "uVT_SLAB" && $slab_idtosubtype{$i} eq "INIT"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVT_PROG,";
    }elsif($slab_idtotype{$i} eq "uVT_SLAB" && $slab_idtosubtype{$i} eq "XCORE"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVT_PROG,";
    }elsif($slab_idtotype{$i} eq "uVT_SLAB" && $slab_idtosubtype{$i} eq "XHYPAPP"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVT_PROG,";
    }elsif($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XCORE"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVU_PROG,";
    }elsif($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XHYPAPP"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVU_PROG,";
    }elsif($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XGUEST"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVU_PROG_GUEST,";
    }elsif($slab_idtotype{$i} eq "uVT_SLAB" && $slab_idtosubtype{$i} eq "XGUEST"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVT_PROG_GUEST,";
    }elsif($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XRICHGUEST"){
        print $fh "\n	        XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST,";
    }else{
        print "\nError: Unknown slab type!";
        exit 1;
    }

    #mempgtbl_cr3 and iotbl_base
    if ($slab_idtotype{$i} eq "VfT_SLAB"){
	#mempgtbl_cr3 for VfT_SLAB points to verified hypervisor slab page table base
	#iotbl_base for VfT_SLAB is not-used

        print $fh "\n        ".$slab_idtodata_addrstart{$slab_nametoid{"geec_prime"}}." + (2 * 4096),";
        print $fh "\n        0x00000000UL,";


    }elsif ( ($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XGUEST") ||
		($slab_idtotype{$i} eq "uVT_SLAB" && $slab_idtosubtype{$i} eq "XGUEST") ||
		($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XRICHGUEST") ){
	#mempgtbl_cr3 for unverified guest slabs point to their corresponding page table base within uapi_slabmempgtbl
	#iotbl_base for unverified guest slabs point to their corresponding io table base within uapi_slabiotbl
        if($g_ugslabcounter > 1){ # TODO: need to bring this in via a conf. variable when we support multiple guest slabs
		print "\nError: Too many unverified guest slabs (max=1)!";
		exit 1;
	}else{
		print $fh "\n        ".$slab_idtodata_addrstart{$slab_nametoid{"uapi_slabmempgtbl"}}." + ($g_ugslabcounter * 4096),";
		#print $fh "\n        ".$slab_idtodata_addrstart{$slab_nametoid{"uapi_slabiotbl"}}." + ($g_ugslabcounter * (3*4096)),";
		print $fh "\n        ".$slab_idtodata_addrstart{$slab_nametoid{"geec_prime"}}." + (3*4096) + ($g_totaluhslabs * 4096) + ($g_totaluhslabs *(3*4096)) + ($g_ugslabcounter * (3*4096)),";
		$g_ugslabcounter = $g_ugslabcounter + 1;
	}

    }else{
	#mempgtbl_cr3 for unverified hypervisor slabs point to their corresponding page table base within prime
	#iotbl_base
        if($g_uhslabcounter >=  $g_totaluhslabmempgtblsets){
		print "\nError: Too many unverified hypervisor slabs (max=$g_totaluhslabmempgtblsets)!";
		exit 1;
        }else{
		print $fh "\n        ".$slab_idtodata_addrstart{$slab_nametoid{"geec_prime"}}." + (3*4096) + ($g_uhslabcounter * 4096),";
		print $fh "\n        ".$slab_idtodata_addrstart{$slab_nametoid{"geec_prime"}}." + (3*4096) + ($g_totaluhslabs *4096) + ($g_uhslabcounter * (3*4096)),";
		$g_uhslabcounter = $g_uhslabcounter + 1;
        }

    }

	#print "Done-1 for $i...\n";


    #slab_tos
    #print $fh "\n	        {";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[1*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[2*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[3*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[4*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[5*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[6*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[7*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	            ((u32)&_slab_$slab_idtoname{$i}_stack_start[8*XMHF_SLAB_STACKSIZE]),";
    #print $fh "\n	        },";
    print $fh "\n	        {";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (1*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (2*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (3*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (4*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (5*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (6*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (7*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	            ".$slab_idtostack_addrstart{$i}."+ (8*XMHF_SLAB_STACKSIZE),";
    print $fh "\n	        },";



    #slab_callcaps
    printf $fh "\n\t0x%08xUL, ", $slab_idtocallmask{$i};

    #slab_uapisupported
    if($slab_idtotype{$i} eq "VfT_SLAB" && $slab_idtosubtype{$i} eq "UAPI"){
        print $fh "\n       true,";
    }else{
        print $fh "\n       false,";
    }

    #slab_uapicaps
    print $fh "\n       {\n";
    print $fh $slab_idtouapifnmask{$i};

    #$j = 0;
    #while( $j < $total_slabs) {
    #    print $fh "\n	    0xFFFFFFFFUL,";
    #    $j=$j+1;
    #}
    print $fh "\n       },";

    #slab_memgrantreadcaps
    if(exists $slab_idtomemgrantreadcaps{$i}){
        printf $fh "\n       0x%08x,", $slab_idtomemgrantreadcaps{$i};
    }else{
        printf $fh "\n       0x00000000UL,";
    }

    #slab_memgrantwritecaps
    if(exists $slab_idtomemgrantwritecaps{$i}){
        printf $fh "\n       0x%08x,", $slab_idtomemgrantreadcaps{$i};
    }else{
        printf $fh "\n       0x00000000UL,";
    }

    #slab_devices
    #if($slab_idtotype{$i} eq "uVU_SLAB" && $slab_idtosubtype{$i} eq "XRICHGUEST"){
    #    print $fh "\n	    {true, 0xFFFFFFFFUL, {0}},";
    #}else{
    #    print $fh "\n	    {false, 0, {0}},";
    #}

    #incl_devices
    print $fh "\n\n".$slab_idtordinclentries{$i};

    #incl_devices_count
    printf $fh "\n0x%08x,", $slab_idtordinclcount{$i};

    #excl_devices
    print $fh "\n\n".$slab_idtordexclentries{$i};

    #excl_devices_count
    printf $fh "\n0x%08x,", $slab_idtordexclcount{$i};


    #slab_physmem_extents
    print $fh "\n	    {";
    print $fh "\n	        {.addr_start = $slab_idtocode_addrstart{$i}, .addr_end = $slab_idtocode_addrend{$i}, .protection = 0},";
    print $fh "\n	        {.addr_start = $slab_idtodata_addrstart{$i}, .addr_end = $slab_idtodata_addrend{$i}, .protection = 0},";
    print $fh "\n	        {.addr_start = $slab_idtostack_addrstart{$i}, .addr_end = $slab_idtostack_addrend{$i}, .protection = 0},";
    print $fh "\n	        {.addr_start = $slab_idtodmadata_addrstart{$i}, .addr_end = $slab_idtodmadata_addrend{$i}, .protection = 0},";
    print $fh "\n	    },";


    #slab memoffset entries
    #$j = 0;
    print $fh "\n	    {";
    #while( $j < $g_maxmemoffsetentries) {
    #    print $fh "\n	    0x00000000UL,";
    #    $j=$j+1;
    #}
    if($g_memoffsets eq "MEMOFFSETS"){
        print $fh $slab_idtomemoffsetstring{$i};
    }else{
        print $fh "0";
    }
    print $fh "\n	    },";


    #slab_entrystub
    print $fh "\n	    $slab_idtocode_addrstart{$i}";

    print $fh "\n	},";
	print $fh "\n";

	#print "FULL Done for $i...\n";


	$i++;
}

print $fh "\n};";

close $fh;


######


















######
# output final binary linker script
######

open($fh, '>', $g_outputfile_linkerscript) or die "Could not open file '$g_outputfile_linkerscript' $!";

print $fh "\n/* autogenerated XMHF linker script */";
print $fh "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";

print $fh "\n#include <xmhf.h>";
print $fh "\n";
print $fh "\n";
print $fh "\nOUTPUT_ARCH(\"i386\")";
print $fh "\n";
print $fh "\nMEMORY";
print $fh "\n{";
print $fh "\n  all (rwxai) : ORIGIN = $g_loadaddr, LENGTH = $g_loadmaxsize";
print $fh "\n  unaccounted (rwxai) : ORIGIN = 0, LENGTH = 0 /* see section .unaccounted at end */";
print $fh "\n}";
print $fh "\nSECTIONS";
print $fh "\n{";
print $fh "\n	. = $g_loadaddr;";
print $fh "\n";


$i =0;
while($i < $g_totalslabs){
    print $fh "\n	.slab_$slab_idtoname{$i} : {";
    print $fh "\n		. = ALIGN(1);";
    print $fh "\n		_objs_slab_$slab_idtoname{$i}/$slab_idtoname{$i}.slo(.slabcode)";
    print $fh "\n		. = ALIGN(1);";
    print $fh "\n		_objs_slab_$slab_idtoname{$i}/$slab_idtoname{$i}.slo(.slabdata)";
    print $fh "\n		. = ALIGN(1);";
    print $fh "\n		_objs_slab_$slab_idtoname{$i}/$slab_idtoname{$i}.slo(.slabstack)";
    print $fh "\n		. = ALIGN(1);";
    print $fh "\n		_objs_slab_$slab_idtoname{$i}/$slab_idtoname{$i}.slo(.slabdmadata)";
    print $fh "\n		. = ALIGN(1);";
    print $fh "\n	} >all=0x0000";
    print $fh "\n";

    $i=$i+1;
}

print $fh "\n";
print $fh "\n	/* this is to cause the link to fail if there is";
print $fh "\n	* anything we didn't explicitly place.";
print $fh "\n	* when this does cause link to fail, temporarily comment";
print $fh "\n	* this part out to see what sections end up in the output";
print $fh "\n	* which are not handled above, and handle them.";
print $fh "\n	*/";
print $fh "\n	.unaccounted : {";
print $fh "\n	*(*)";
print $fh "\n	} >unaccounted";
print $fh "\n}";
print $fh "\n";


close $fh;


######










exit 0;
















