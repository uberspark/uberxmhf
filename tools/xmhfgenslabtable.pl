#!/usr/bin/perl
# script to generate XMHF slab physical memory extents
# based on the slab names provided
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;
use File::Basename;

chomp(my $filename = $ARGV[0]);
tie my @array, 'Tie::File', $filename or die $!;

my $i = 0;
my %slabrecord;
my $slabname;
my $slabtype;

my @slabnamearray;
my @slabtypearray;

while( $i <= $#array) {

    my $line = $array[$i];
    chomp($line);

    my $trimline = $line;
    $trimline =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace

    # split the line using the comma delimiter
    my @slabinfo = split(/,/, $trimline);
    #print "Processing line: $line \n";

    $slabname = basename($slabinfo[0]);
    $slabname =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
    $slabtype = $slabinfo[1];
    $slabtype =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace


    #print "Slab name: $slabname, type:$slabtype ...\n";
    push @slabnamearray, $slabname;
    push @slabtypearray, $slabtype;

    # move on to the next line
    $i = $i + 1;
}


$i =0;

print "\n/* autogenerated XMHF/GEEC sentinel slab info table */";
print "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";

print "\n";

while( $i <= $#slabnamearray) {
	print "\n";
	print "\nextern u8 _slab_$slabnamearray[$i]_code_start[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_code_end[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_data_start[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_data_end[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_stack_start[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_stack_end[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_dmadata_start[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_dmadata_end[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_mmio_start[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_mmio_end[];";
	print "\nextern u8 _slab_$slabnamearray[$i]_entrypoint[];";

	$i++;
}

print "\n";
print "\n__attribute__(( section(\".data\") )) __attribute__((aligned(4096))) x_slab_info_t _xmhfhic_common_slab_info_table[] = {";


$i = 0;
while( $i <= $#slabnamearray ){
	print "\n";
    print "\n	//$slabnamearray[$i]";
    print "\n	{";
    print "\n	    {";

    if($slabtypearray[$i] eq "VfT_PROG_PRIME"){
        print "\n	        XMHFGEEC_SLABTYPE_VfT_PROG_PRIME,";
    }elsif($slabtypearray[$i] eq "VfT_PROG"){
        print "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,";
    }elsif($slabtypearray[$i] eq "VfT_PROG_EXCEPTION"){
        print "\n	        XMHFGEEC_SLABTYPE_VfT_PROG_EXCEPTION,";
    }elsif($slabtypearray[$i] eq "uVU_PROG"){
        print "\n	        XMHFGEEC_SLABTYPE_uVU_PROG,";
    }elsif($slabtypearray[$i] eq "uVU_PROG_GUEST"){
        print "\n	        XMHFGEEC_SLABTYPE_uVU_PROG_GUEST,";
    }elsif($slabtypearray[$i] eq "uVT_PROG_GUEST"){
        print "\n	        XMHFGEEC_SLABTYPE_uVT_PROG_GUEST,";
    }elsif($slabtypearray[$i] eq "uVU_PROG_RICHGUEST"){
        print "\n	        XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST,";
    }else{
        print "\nError: Unknown slab type!";
        exit 1;
    }

    print "\n	        false,";
    print "\n	        false,";

    printf "\n	        &_slab_uapi_slabmempgtbl_data_start[%u],", ($i * 4096);

    print "\n	        {";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[1*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[2*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[3*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[4*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[5*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[6*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[7*XMHF_SLAB_STACKSIZE]),";
    print "\n	            ((u32)&_slab_$slabnamearray[$i]_stack_start[8*XMHF_SLAB_STACKSIZE]),";
    print "\n	        }";
    print "\n	    },";
    print "\n	    true,";
    print "\n	    0,";
    print "\n       0,";
    print "\n	    0,";

    if($slabtypearray[$i] eq "uVU_PROG_RICHGUEST"){
        print "\n	    {true, 0xFFFFFFFFUL, {0}},";
    }else{
        print "\n	    {false, 0, {0}},";
    }

    print "\n	    {";
    print "\n	        {.addr_start = _slab_$slabnamearray[$i]_code_start, .addr_end = _slab_$slabnamearray[$i]_code_end, .protection = 0},";
    print "\n	        {.addr_start = _slab_$slabnamearray[$i]_data_start, .addr_end = _slab_$slabnamearray[$i]_data_end, .protection = 0},";
    print "\n	        {.addr_start = _slab_$slabnamearray[$i]_stack_start, .addr_end = _slab_$slabnamearray[$i]_stack_end, .protection = 0},";
    print "\n	        {.addr_start = _slab_$slabnamearray[$i]_dmadata_start, .addr_end = _slab_$slabnamearray[$i]_dmadata_end, .protection = 0},";
    print "\n	        {.addr_start = _slab_$slabnamearray[$i]_mmio_start, .addr_end = _slab_$slabnamearray[$i]_mmio_end, .protection = 0},";
    print "\n	    },";
    print "\n	    (u32)_slab_$slabnamearray[$i]_entrypoint";
    print "\n	},";
	print "\n";

	$i++;
}

print "\n};";


#while( $i <= $#slabnamearray) {
#    printf "Slab name: %s, Type: %s\n", $slabnamearray[$i], $slabtypearray[$i];
#    $i = $i + 1;
#}


exit 0;






















