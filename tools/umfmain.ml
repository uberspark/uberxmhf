(*
	frama-c plugin for manifest parsing (main module)
	author: amit vasudevan (amitvasudevan@acm.org)
*)
open Umfcommon

module Self = Plugin.Register
	(struct
		let name = "US manifest parser"
		let shortname = "umf"
		let help = "UberSpark manifest parsing plugin"
	end)


module Cmdopt_slabsfile = Self.String
	(struct
		let option_name = "-umf-uobjlist"
		let default = ""
		let arg_name = "uobjlist-file"
		let help = "uobj list file"
	end)

module Cmdopt_outputfile_slabinfotable = Self.String
	(struct
		let option_name = "-umf-outuobjinfotable"
		let default = ""
		let arg_name = "outuobjinfotable-file"
		let help = "output uobj info table filename"
	end)

module Cmdopt_outputfile_linkerscript = Self.String
	(struct
		let option_name = "-umf-outlinkerscript"
		let default = ""
		let arg_name = "outlinkerscript-file"
		let help = "output linker script filename"
	end)

module Cmdopt_loadaddr = Self.String
	(struct
		let option_name = "-umf-loadaddr"
		let default = ""
		let arg_name = "load-address"
		let help = "load memory address of binary"
	end)

module Cmdopt_loadmaxsize = Self.String
	(struct
		let option_name = "-umf-loadmaxsize"
		let default = ""
		let arg_name = "loadmax-size"
		let help = "max load memory address of binary"
	end)

module Cmdopt_totaluhslabs = Self.String
	(struct
		let option_name = "-umf-totaluhuobjs"
		let default = ""
		let arg_name = "total-uhuobjs"
		let help = "total number of unverified uobjs"
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
		let default = false
		let help = "when on (off by default), include absolute memory offsets in MEMOFFSETS list"
	end)


(*
	**************************************************************************
	global variables
	**************************************************************************
*)

(*	command line inputs *)
let g_slabsfile = ref "";;	(* argv 0 *)
let g_outputfile_slabinfotable = ref "";; (* argv 1 *)
let g_outputfile_linkerscript = ref "";; (* argv 2 *)
let g_loadaddr = ref 0x0;; (* argv 3 *)
let g_loadmaxsize = ref 0x0;; (* argv 4 *)
let g_totaluhslabs = ref 0;; (* argv 5 *)
(* let g_maxincldevlistentries = ref 0;; *) (* argv 6 *)
(* let g_maxexcldevlistentries = ref 0;; *) (* argv 7 *)
(* let g_maxmemoffsetentries = ref 0;; *) (* argv 8 *)
let g_memoffsets = ref false;; (*argv 9 *)

(* other global variables *)
let g_totalslabmempgtblsets = ref 0;;
let g_totalslabiotblsets = ref 0;;
let g_uhslabcounter = ref 0;;
let g_ugslabcounter = ref 0;;
let g_rootdir = ref "";;
let i = ref 0;;
let g_memmapaddr = ref 0x0;;
(* let fh : in_channel;; *)
let g_totaluhslabmempgtblsets = ref 0;;
let g_totaluvslabiotblsets = ref 0;;


(* global hash table variables *)
let slab_idtodata_addrstart = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtodata_addrend = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtocode_addrstart = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtocode_addrend = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtostack_addrstart = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtostack_addrend = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtodmadata_addrstart = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtodmadata_addrend = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;



let umf_process_cmdline () =
	g_slabsfile := Cmdopt_slabsfile.get();
	g_outputfile_slabinfotable := Cmdopt_outputfile_slabinfotable.get();
	g_outputfile_linkerscript := Cmdopt_outputfile_linkerscript.get();
	g_loadaddr := int_of_string (Cmdopt_loadaddr.get());
	g_loadmaxsize := int_of_string (Cmdopt_loadmaxsize.get());
	g_totaluhslabs := int_of_string (Cmdopt_totaluhslabs.get());
	g_maxincldevlistentries := int_of_string (Cmdopt_maxincldevlistentries.get());
	g_maxexcldevlistentries := int_of_string (Cmdopt_maxexcldevlistentries.get());
	g_maxmemoffsetentries := int_of_string (Cmdopt_maxmemoffsetentries.get());
	if Cmdopt_memoffsets.get() then g_memoffsets := true else g_memoffsets := false;

	
	Self.result "g_slabsfile=%s\n" !g_slabsfile;
	Self.result "g_outputfile_slabinfotable=%s\n" !g_outputfile_slabinfotable;
	Self.result "g_outputfile_linkerscript=%s\n" !g_outputfile_linkerscript;
	Self.result "g_loadaddr=0x%x\n" !g_loadaddr;
	Self.result "g_loadmaxsize=0x%x\n" !g_loadmaxsize;
	Self.result "g_totaluhslabs=%d\n" !g_totaluhslabs;
	Self.result "g_maxincldevlistentries=%d\n" !g_maxincldevlistentries;
	Self.result "g_maxexcldevlistentries=%d\n" !g_maxexcldevlistentries;
	Self.result "g_maxmemoffsetentries=%d\n" !g_maxmemoffsetentries;
	Self.result "g_memoffsets=%b\n" !g_memoffsets;
	()

let umf_compute_memory_map () =
	i := 0;
	g_memmapaddr := !g_loadaddr;

	Self.result "Proceeding to compute memory map...\n";
	
	while (!i < !g_totalslabs) do
	    Hashtbl.add slab_idtocode_addrstart !i  (Printf.sprintf "0x%08x" !g_memmapaddr);
    	g_memmapaddr := !g_memmapaddr + (Hashtbl.find slab_idtocodesize !i);
    	Hashtbl.add slab_idtocode_addrend !i (Printf.sprintf "0x%08x" !g_memmapaddr);

	    Hashtbl.add slab_idtodata_addrstart !i (Printf.sprintf "0x%08x" !g_memmapaddr);
    	g_memmapaddr := !g_memmapaddr + (Hashtbl.find slab_idtodatasize !i);
    	Hashtbl.add slab_idtodata_addrend !i (Printf.sprintf "0x%08x" !g_memmapaddr);

	    Hashtbl.add slab_idtostack_addrstart !i (Printf.sprintf "0x%08x" !g_memmapaddr);
    	g_memmapaddr := !g_memmapaddr + (Hashtbl.find slab_idtostacksize !i);
    	Hashtbl.add slab_idtostack_addrend !i (Printf.sprintf "0x%08x" !g_memmapaddr);

    	Hashtbl.add slab_idtodmadata_addrstart !i (Printf.sprintf "0x%08x" !g_memmapaddr);
    	g_memmapaddr := !g_memmapaddr + (Hashtbl.find slab_idtodmadatasize !i);
    	Hashtbl.add slab_idtodmadata_addrend !i (Printf.sprintf "0x%08x" !g_memmapaddr);	

    	i := !i + 1;
	done;

	Self.result "Computed memory map\n";

	i := 0;
	while (!i < !g_totalslabs) do
	    Self.result "slabname: %s \n" (Hashtbl.find slab_idtoname !i);
	    Self.result "code    - addrstart= %s, addrend=%s \n" (Hashtbl.find slab_idtocode_addrstart !i) (Hashtbl.find slab_idtocode_addrend !i);
	    Self.result "data    - addrstart= %s, addrend=%s \n" (Hashtbl.find slab_idtodata_addrstart !i) (Hashtbl.find slab_idtodata_addrend !i);
	    Self.result "stack   - addrstart= %s, addrend=%s \n" (Hashtbl.find slab_idtostack_addrstart !i) (Hashtbl.find slab_idtostack_addrend !i);
	    Self.result "dmadata - addrstart= %s, addrend=%s \n" (Hashtbl.find slab_idtodmadata_addrstart !i) (Hashtbl.find slab_idtodmadata_addrend !i);
		i := !i + 1;
	done;


	()
	
let run () =
	Self.result "Parsing manifest...\n";
	umf_process_cmdline ();

	g_rootdir := (Filename.dirname !g_slabsfile) ^ "/";
	Self.result "g_rootdir=%s\n" !g_rootdir;

	g_totaluhslabmempgtblsets := !g_totaluhslabs;
	g_totaluvslabiotblsets := !g_totaluhslabs;
	g_totalslabmempgtblsets := !g_totaluhslabmempgtblsets + 2;
	g_totalslabiotblsets := !g_totaluvslabiotblsets + 2;
	g_uhslabcounter := 0;
	g_ugslabcounter := 0;

	umfcommon_init !g_slabsfile !g_memoffsets !g_rootdir;
	Self.result "g_totalslabs=%d \n" !g_totalslabs;
	
	umf_compute_memory_map ();

	Self.result "Done.\n";
	()

(*
	Format.printf "Parsing manifest...\n";
	Umfcommon.subrun();
	Hashtbl.add m_hash "h" "hello";
	Format.printf "back into this module.\n";
	()
*)

let () = Db.Main.extend run

