(*
	frama-c plugin for composition check
	author: amit vasudevan (amitvasudevan@acm.org)
*)
open Umfcommon

module Self = Plugin.Register
	(struct
		let name = "US composition check"
		let shortname = "ucvf"
		let help = "UberSpark composition check"
	end)


module Cmdopt_slabsfile = Self.String
	(struct
		let option_name = "-umf-uobjlist"
		let default = ""
		let arg_name = "uobjlist-file"
		let help = "uobj list file"
	end)

module Cmdopt_outputfile_ccompdriverfile = Self.String
	(struct
		let option_name = "-umf-outuobjccompdriver"
		let default = ""
		let arg_name = "outuobjccompdriver-file"
		let help = "output uobj composition check driver file"
	end)


module Cmdopt_outputfile_ccompcheckfile = Self.String
	(struct
		let option_name = "-umf-outuobjccompcheck"
		let default = ""
		let arg_name = "outuobjccompcheck-file"
		let help = "output uobj composition check file"
	end)


module Cmdopt_maxincldevlistentries = Self.String
	(struct
		let option_name = "-umf-maxincldevlistentries"
		let default = ""
		let arg_name = "max-incldevlistentries"
		let help = "total number of INCL device list entries"
	end)

module Cmdopt_maxexcldevlistentries = Self.String
	(struct
		let option_name = "-umf-maxexcldevlistentries"
		let default = ""
		let arg_name = "max-excldevlistentries"
		let help = "total number of EXCL device list entries"
	end)

module Cmdopt_maxmemoffsetentries = Self.String
	(struct
		let option_name = "-umf-maxmemoffsetentries"
		let default = ""
		let arg_name = "max-memoffsetentries"
		let help = "total number of MEMOFFSET entries"
	end)

module Cmdopt_memoffsets = Self.False
	(struct
		let option_name = "-umf-memoffsets"
		(* let default = false *)
		let help = "when on (off by default), include absolute memory offsets in MEMOFFSETS list"
	end)


(*
	**************************************************************************
	global variables
	**************************************************************************
*)

(*	command line inputs *)
let g_slabsfile = ref "";;	(* argv 0 *)
let g_outputfile_ccompdriverfile = ref "";; (* argv 1 *)
let g_outputfile_ccompcheckfile = ref "";; (* argv 2 *)
(* let g_maxincldevlistentries = ref 0;; *) (* argv 3 *)
(* let g_maxexcldevlistentries = ref 0;; *) (* argv 4 *)
(* let g_maxmemoffsetentries = ref 0;; *) (* argv 5 *)
let g_memoffsets = ref false;; (*argv 6 *)

(* other global variables *)
let g_rootdir = ref "";;



let uccomp_process_cmdline () =
	g_slabsfile := Cmdopt_slabsfile.get();
	g_outputfile_ccompdriverfile := Cmdopt_outputfile_ccompdriverfile.get();
	g_outputfile_ccompcheckfile := Cmdopt_outputfile_ccompcheckfile.get();
	g_maxincldevlistentries := int_of_string (Cmdopt_maxincldevlistentries.get());
	g_maxexcldevlistentries := int_of_string (Cmdopt_maxexcldevlistentries.get());
	g_maxmemoffsetentries := int_of_string (Cmdopt_maxmemoffsetentries.get());
	if Cmdopt_memoffsets.get() then g_memoffsets := true else g_memoffsets := false;

	
	Self.result "g_slabsfile=%s\n" !g_slabsfile;
	Self.result "g_outputfile_ccompdriverfile=%s\n" !g_outputfile_ccompdriverfile;
	Self.result "g_outputfile_ccompcheckfile=%s\n" !g_outputfile_ccompcheckfile;
	Self.result "g_maxincldevlistentries=%d\n" !g_maxincldevlistentries;
	Self.result "g_maxexcldevlistentries=%d\n" !g_maxexcldevlistentries;
	Self.result "g_maxmemoffsetentries=%d\n" !g_maxmemoffsetentries;
	Self.result "g_memoffsets=%b\n" !g_memoffsets;
	()



	
let run () =
	Self.result "Generating composition check files...\n";
	uccomp_process_cmdline ();

	g_rootdir := (Filename.dirname !g_slabsfile) ^ "/";
	Self.result "g_rootdir=%s\n" !g_rootdir;

	umfcommon_init !g_slabsfile !g_memoffsets !g_rootdir;
	Self.result "g_totalslabs=%d \n" !g_totalslabs;
	
	
	Self.result "Done.\n";
	()


let () = Db.Main.extend run

