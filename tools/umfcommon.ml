(*
	frama-c plugin for manifest parsing (common library module)
	author: amit vasudevan (amitvasudevan@acm.org)
*)


(*
	**************************************************************************
	global variables
	**************************************************************************
*)
let g_totalslabs = ref 0;;


let slab_idtodir = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtogsm = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtommapfile = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtoname = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtotype = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtosubtype = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_nametoid = ((Hashtbl.create 32) : ((string,int)  Hashtbl.t));;



(*
	**************************************************************************
	global interfaces
	**************************************************************************
*)

let left_pos s len =
  let rec aux i =
    if i >= len then None
    else match s.[i] with
    | ' ' | '\n' | '\t' | '\r' -> aux (succ i)
    | _ -> Some i
  in
  aux 0
 
let right_pos s len =
  let rec aux i =
    if i < 0 then None
    else match s.[i] with
    | ' ' | '\n' | '\t' | '\r' -> aux (pred i)
    | _ -> Some i
  in
  aux (pred len)
  
let trim s =
  let len = String.length s in
  match left_pos s len, right_pos s len with
  | Some i, Some j -> String.sub s i (j - i + 1)
  | None, None -> ""
  | _ -> assert false


let umfcommon_init g_slabsfile g_memoffsets g_rootdir = 
	let i = ref 0 in
	let slabdir = ref "" in
	let slabname = ref "" in  
	let slabtype = ref "" in
	let slabsubtype = ref "" in
	let slabgsmfile = ref "" in
	let slabmmapfile = ref "" in
	let sfh = open_in g_slabsfile in
	let trimline = ref "" in

		Format.printf "g_slabsfile=%s\n" g_slabsfile;
		Format.printf "g_memoffsets=%b\n" g_memoffsets;
		Format.printf "g_rootdir=%s\n" g_rootdir;
			
		try
    		while true do
      			trimline := trim (input_line sfh);
				let slabinfo = Str.split (Str.regexp ",") !trimline in
					slabdir := trim (List.nth slabinfo 0);
					slabname := Filename.basename !slabdir; 
					slabtype := trim (List.nth slabinfo 1);
					slabsubtype := trim (List.nth slabinfo 2);
				    slabgsmfile := !slabdir ^ "/" ^ !slabname ^ ".gsm.pp";
	    			slabmmapfile := g_rootdir ^ "_objects/_objs_slab_" ^ !slabname ^ "/" ^ !slabname ^ ".mmap";

	    			Hashtbl.add slab_idtodir !i !slabdir;
	    			Hashtbl.add slab_idtoname !i !slabname;
	    			Hashtbl.add slab_idtotype !i !slabtype;
	    			Hashtbl.add slab_idtosubtype !i !slabsubtype;
	    			Hashtbl.add slab_idtogsm !i !slabgsmfile;
	    			Hashtbl.add slab_idtommapfile !i !slabmmapfile;
	    			Hashtbl.add slab_nametoid !slabname !i;

					
					Format.printf "%s\n" !trimline;      			
					(*
					Format.printf "  slabdir=%s\n" !slabdir;      			
					Format.printf "  slabname=%s\n" !slabname;      			
					Format.printf "  slabtype=%s\n" !slabtype;      			
					Format.printf "  slabsubtype=%s\n" !slabsubtype;      			
					Format.printf "  slabgsmfile=%s\n" !slabgsmfile;      			
					Format.printf "  slabmmapfile=%s\n" !slabmmapfile;      			
					*)
					
					i := !i + 1;
		    done;
		with End_of_file -> 
    			close_in sfh;
    	;		

		g_totalslabs := !i;
		Format.printf "total slabs=%d\n" !g_totalslabs;      			

		(* now iterate through all the slab id's and populate callmask and uapimasks *)
		i := 0;
		while (!i < !g_totalslabs) do
	    	begin
				Format.printf "  slabdir=%s\n" (Hashtbl.find slab_idtodir !i);      			
				Format.printf "  slabname=%s\n" (Hashtbl.find slab_idtoname !i);      			
				Format.printf "  slabtype=%s\n" (Hashtbl.find slab_idtotype !i);      			
				Format.printf "  slabsubtype=%s\n" (Hashtbl.find slab_idtosubtype !i);      			
				Format.printf "  slabgsmfile=%s\n" (Hashtbl.find slab_idtogsm !i);      			
				Format.printf "  slabmmapfile=%s\n" (Hashtbl.find slab_idtommapfile !i);      			
			
				if g_memoffsets then
					begin
						(* 
						parse_mmap($slab_idtommapfile{$i}, $i, $g_totalslabs);
						$slab_idtouapifnmask{$i} = parse_gsm($slab_idtogsm{$i}, $i, $g_totalslabs, 1);
						*)
					end
				else
					begin
						(*
						$slab_idtouapifnmask{$i} = parse_gsm($slab_idtogsm{$i}, $i, $g_totalslabs, 0);
						*)
					end
				;				    	

	    		i := !i + 1;
			end
		done;



		
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

