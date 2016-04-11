(*
	frama-c plugin for manifest parsing (main module)
	author: amit vasudevan (amitvasudevan@acm.org)
*)
open Umfcommon


(*
	**************************************************************************
	global variables
	**************************************************************************
*)

(*	command line inputs *)

(*
my $g_slabsfile = $ARGV[0];
my $g_outputfile_slabinfotable = $ARGV[1];
my $g_outputfile_linkerscript = $ARGV[2];
my $g_loadaddr = $ARGV[3];
my $g_loadmaxsize = $ARGV[4];
my $g_totaluhslabs = $ARGV[5];
$g_maxincldevlistentries = $ARGV[6];
$g_maxexcldevlistentries = $ARGV[7];
$g_maxmemoffsetentries = $ARGV[8];
my $g_memoffsets = $ARGV[9];
*)

let g_slabsfile : string = "";;
let g_outputfile_slabinfotable : string = "";;
let g_outputfile_linkerscript : string = "";;
let g_loadaddr : int = 0x0;;
let g_loadmaxsize : int = 0x0;;
let g_totaluhslabs : int = 0;;
let g_maxincldevlistentries : int = 0;;
let g_maxexcldevlistentries : int = 0;;
let g_maxmemoffsetentries : int = 0;;
let g_memoffsets : bool = false;;




let run () =
	Format.printf "proceeding to invoke function within another module...\n";
	Umfcommon.subrun();
	Hashtbl.add m_hash "h" "hello";
	Format.printf "back into this module.\n";
	()

let () = Db.Main.extend run

