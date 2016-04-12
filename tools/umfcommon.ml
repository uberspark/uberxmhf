(*
	frama-c plugin for manifest parsing (common library module)
	author: amit vasudevan (amitvasudevan@acm.org)
*)

let m_hash = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;
      
let subrun () =
	Format.printf "hello world from sub module\n";
	Format.printf "returning back to main module\n";
	()

let umfcommon_init g_slabsfile g_memoffsets g_rootdir = 
	Format.printf "g_slabsfile=%s\n" g_slabsfile;
	Format.printf "g_memoffsets=%b\n" g_memoffsets;
	Format.printf "g_rootdir=%s\n" g_rootdir;
	()

(*
sub upmf_init {
	my($g_slabsfile, $g_memoffsets, $g_rootdir) = @_;
	my $i=0;
	my $slabdir;
	my $slabname;
	my $slabtype;
	my $slabsubtype;
	my $slabgsmfile;
	my $slabmmapfile;

	#print "upmf_init: ", $g_slabsfile,",", $g_memoffsets, ",", $g_rootdir, "\n";

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
	    $slabgsmfile = $slabdir."/".$slabname.".gsm.pp";
	    $slabmmapfile = $g_rootdir."_objects/_objs_slab_".$slabname."/".$slabname.".mmap";

	    #print "Slab name: $slabname, mmap:$slabmmapfile, gsm:$slabgsmfile ...\n";
	    $slab_idtodir{$i} = $slabdir;
	    $slab_idtogsm{$i} = $slabgsmfile;
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


}
*)

