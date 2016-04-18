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



let umf_configure_slabs () =
	let l_cmdline = ref "" in
	
	Self.result "Proceeding to configure slabs...\n";

	if (!g_memoffsets) then
		begin
			(* no configuration needed when doing real build *)
		end
	else
		begin
		    i := 0;
		    while (!i < !g_totalslabs) do
		        Self.result "Configuring slab: %s with type: %s:%s ...\n" (Hashtbl.find slab_idtodir !i) (Hashtbl.find slab_idtotype !i) (Hashtbl.find slab_idtosubtype !i);
		        l_cmdline := 	(Printf.sprintf "cd %s%s && ../../configure_slab " !g_rootdir (Hashtbl.find slab_idtodir !i)) ^
		                	 	(Printf.sprintf " --with-slabtype=%s" (Hashtbl.find slab_idtotype !i)) ^
		                		(Printf.sprintf " --with-slabsubtype=%s" (Hashtbl.find slab_idtosubtype !i)) ^
		                		(Printf.sprintf " --with-slabcodestart=%s" (Hashtbl.find slab_idtocode_addrstart !i)) ^
		                		(Printf.sprintf " --with-slabcodeend=%s" (Hashtbl.find slab_idtocode_addrend !i)) ^
		                		(Printf.sprintf " --with-slabdatastart=%s" (Hashtbl.find slab_idtodata_addrstart !i)) ^
		                		(Printf.sprintf " --with-slabdataend=%s" (Hashtbl.find slab_idtodata_addrend !i)) ^
		                		(Printf.sprintf " --with-slabstackstart=%s" (Hashtbl.find slab_idtostack_addrstart !i)) ^
		                		(Printf.sprintf " --with-slabstackend=%s" (Hashtbl.find slab_idtostack_addrend !i)) ^
		                		(Printf.sprintf " --with-slabdmadatastart=%s" (Hashtbl.find slab_idtodmadata_addrstart !i)) ^
		                		(Printf.sprintf " --with-slabdmadataend=%s" (Hashtbl.find slab_idtodmadata_addrend !i)) ^
		                		(Printf.sprintf " >/dev/null 2>&1");
		        ignore(Sys.command !l_cmdline);
		        i := !i + 1;
		    done;

		end
	;

	Self.result "Slabs configured.\n";
	()
	


let umf_output_infotable () =
    let oc = open_out !g_outputfile_slabinfotable in

	Printf.fprintf oc "\n/* autogenerated XMHF/GEEC sentinel slab info table */";
	Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
	Printf.fprintf oc "\n";
	Printf.fprintf oc "\n";
	Printf.fprintf oc "\n__attribute__(( section(\".data\") )) __attribute__((aligned(4096))) xmhfgeec_slab_info_t xmhfgeec_slab_info_table[] = {";

	i := 0;
	while (!i < !g_totalslabs ) do
		(* slab name *)
		(* Self.result "Looping for slab %d..." !i; *)
		Printf.fprintf oc "\n";
	    Printf.fprintf oc "\n	//%s" (Hashtbl.find slab_idtoname !i);
	    Printf.fprintf oc "\n	{";
	
	    (* slab_inuse *)
	    Printf.fprintf oc "\n	    true,";

		(* slab type *)
	    if ( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    	 (compare (Hashtbl.find slab_idtosubtype !i) "PRIME") = 0 ) then 
        	Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "SENTINEL") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_SENTINEL,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "INIT") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XCORE") = 0 ) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XHYPAPP") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    		 (compare (Hashtbl.find slab_idtosubtype !i) "UAPI") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0  && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "EXCEPTION") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	    		 (compare (Hashtbl.find slab_idtosubtype !i) "INTERCEPT") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_VfT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "INIT") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XCORE") = 0 ) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVT_SLAB") = 0 && 
	             (compare (Hashtbl.find slab_idtosubtype !i) "XHYPAPP") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVT_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVU_SLAB") = 0 && 
	    		 (compare (Hashtbl.find slab_idtosubtype !i) "XCORE") = 0 ) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVU_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVU_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XHYPAPP") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVU_PROG,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVU_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XGUEST") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVU_PROG_GUEST,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVT_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XGUEST") = 0) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVT_PROG_GUEST,"
	    else if( (compare (Hashtbl.find slab_idtotype !i) "uVU_SLAB") = 0 && 
	    	     (compare (Hashtbl.find slab_idtosubtype !i) "XRICHGUEST") = 0 ) then
	        Printf.fprintf oc "\n	        XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST,"
	    else
	    	begin
	        	Self.result "Error: Unknown slab type!\n";
	        	ignore(exit 1);
	    	end
	    ;


	    (* mempgtbl_cr3 and iotbl_base *)
    	if ( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0) then
    		begin
				(* mempgtbl_cr3 for VfT_SLAB points to verified hypervisor slab page table base *)
				(* iotbl_base for VfT_SLAB is not-used *)
		        Printf.fprintf oc "\n        %s  + (2 * 4096)," (Hashtbl.find slab_idtodata_addrstart (Hashtbl.find slab_nametoid "geec_prime") );
	    	    Printf.fprintf oc "\n        0x00000000UL,";
			end
		
	    else if ( ((compare (Hashtbl.find slab_idtotype !i) "uVU_SLAB") = 0 && (compare (Hashtbl.find slab_idtosubtype !i) "XGUEST") = 0) ||
				  ((compare (Hashtbl.find slab_idtotype !i) "uVT_SLAB") = 0 && (compare (Hashtbl.find slab_idtosubtype !i) "XGUEST") = 0) ||
				  ((compare (Hashtbl.find slab_idtotype !i) "uVU_SLAB") = 0 && (compare (Hashtbl.find slab_idtosubtype !i) "XRICHGUEST") = 0) ) then
			begin
				(* mempgtbl_cr3 for unverified guest slabs point to their corresponding page table base within uapi_slabmempgtbl *)
				(* iotbl_base for unverified guest slabs point to their corresponding io table base within uapi_slabiotbl *)
		        if (!g_ugslabcounter > 1) then
		        	begin 
		        		(* TODO: need to bring this in via a conf. variable when we support multiple guest slabs *)
						Self.result "Error: Too many unverified guest slabs (max=1)!\n";
						ignore(exit 1);
					end
				else
					begin
						Printf.fprintf oc "\n        %s  + (%d * 4096)," (Hashtbl.find slab_idtodata_addrstart (Hashtbl.find slab_nametoid "uapi_slabmempgtbl"))  !g_ugslabcounter;
						Printf.fprintf oc "\n        %s  + (3*4096) + (%d * 4096) + (%d *(3*4096)) + (%d * (3*4096))," (Hashtbl.find slab_idtodata_addrstart (Hashtbl.find slab_nametoid "geec_prime")) !g_totaluhslabs !g_totaluhslabs !g_ugslabcounter;
						g_ugslabcounter := !g_ugslabcounter + 1;
					end
				;
			end
			
	    else
			begin
				(* mempgtbl_cr3 for unverified hypervisor slabs point to their corresponding page table base within prime *)
				(* iotbl_base *)
		        if(!g_uhslabcounter >=  !g_totaluhslabmempgtblsets) then
		        	begin
						Self.result "Error: Too many unverified hypervisor slabs (max=%d)!\n" !g_totaluhslabmempgtblsets;
						ignore(exit 1);
					end
		        else
		        	begin
						Printf.fprintf oc "\n        %s + (3*4096) + (%d * 4096)," (Hashtbl.find slab_idtodata_addrstart (Hashtbl.find slab_nametoid "geec_prime")) !g_uhslabcounter;
						Printf.fprintf oc "\n        %s + (3*4096) + (%d *4096) + (%d * (3*4096)), " (Hashtbl.find slab_idtodata_addrstart (Hashtbl.find slab_nametoid "geec_prime")) !g_totaluhslabs !g_uhslabcounter;
						g_uhslabcounter := !g_uhslabcounter + 1;
		        	end
		        ;
			end
	    ;


	    (* slab_tos *)
	    Printf.fprintf oc "\n	        {";
	    Printf.fprintf oc "\n	            %s + (1*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (2*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (3*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (4*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (5*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (6*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (7*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	            %s + (8*XMHF_SLAB_STACKSIZE)," (Hashtbl.find slab_idtostack_addrstart !i);
	    Printf.fprintf oc "\n	        },";

	    (* slab_callcaps *)
	    if (Hashtbl.mem slab_idtocallmask !i) then
	    	begin
	    	    Printf.fprintf oc "\n\t0x%08xUL, " (Hashtbl.find slab_idtocallmask !i);
	    	end
	    else
	    	begin
	    		Self.result "No callcaps for slab id %d, using 0\n" !i;
	    		Printf.fprintf oc "\n\t0x00000000UL, ";
	    	end
	    ;
	
	    (* slab_uapisupported *)
	    if( (compare (Hashtbl.find slab_idtotype !i) "VfT_SLAB") = 0 && 
	        (compare (Hashtbl.find slab_idtosubtype !i) "UAPI") = 0) then
	        Printf.fprintf oc "\n       true,"
	    else
	        Printf.fprintf oc "\n       false,"
	    ;
	
	    (* slab_uapicaps *)
	    Printf.fprintf oc "\n       {\n";
	    Printf.fprintf oc "%s" (Hashtbl.find slab_idtouapifnmask !i);
	    Printf.fprintf oc "\n       },";

	    (* slab_memgrantreadcaps *)
	    if(Hashtbl.mem slab_idtomemgrantreadcaps !i) then
	        Printf.fprintf oc "\n       0x%08x," (Hashtbl.find slab_idtomemgrantreadcaps !i)
	    else
	        Printf.fprintf oc "\n       0x00000000UL,"
	    ;

	    (* slab_memgrantwritecaps *)
	    if(Hashtbl.mem slab_idtomemgrantwritecaps !i) then
	        Printf.fprintf oc "\n       0x%08x," (Hashtbl.find slab_idtomemgrantreadcaps !i)
	    else
	        Printf.fprintf oc "\n       0x00000000UL,"
	    ;

    	(* incl_devices *)
    	Printf.fprintf oc "\n\n%s" (Hashtbl.find slab_idtordinclentries !i);

    	(* incl_devices_count *)
    	Printf.fprintf oc "\n0x%08x," (Hashtbl.find slab_idtordinclcount !i);

    	(* excl_devices *)
    	Printf.fprintf oc "\n\n%s" (Hashtbl.find slab_idtordexclentries !i);

    	(* excl_devices_count *)
    	Printf.fprintf oc "\n0x%08x," (Hashtbl.find slab_idtordexclcount !i);

	    (* slab_physmem_extents *)
	    Printf.fprintf oc "\n	    {";
	    Printf.fprintf oc "\n	        {.addr_start = %s, .addr_end = %s, .protection = 0}," (Hashtbl.find slab_idtocode_addrstart !i) (Hashtbl.find slab_idtocode_addrend !i);
	    Printf.fprintf oc "\n	        {.addr_start = %s, .addr_end = %s, .protection = 0}," (Hashtbl.find slab_idtodata_addrstart !i) (Hashtbl.find slab_idtodata_addrend !i);
	    Printf.fprintf oc "\n	        {.addr_start = %s, .addr_end = %s, .protection = 0}," (Hashtbl.find slab_idtostack_addrstart !i) (Hashtbl.find slab_idtostack_addrend !i);
	    Printf.fprintf oc "\n	        {.addr_start = %s, .addr_end = %s, .protection = 0}," (Hashtbl.find slab_idtodmadata_addrstart !i) (Hashtbl.find slab_idtodmadata_addrend !i);
	    Printf.fprintf oc "\n	    },";

	    (* slab memoffset entries *)
	    Printf.fprintf oc "\n	    {";
	    if(!g_memoffsets) then
	        Printf.fprintf oc "%s" (Hashtbl.find slab_idtomemoffsetstring !i)
	    else
	        Printf.fprintf oc "0"
	    ;
	    Printf.fprintf oc "\n	    },";


	    (* slab_entrystub *)
	    Printf.fprintf oc "\n	    %s" (Hashtbl.find slab_idtocode_addrstart !i);

	    Printf.fprintf oc "\n	},";
		Printf.fprintf oc "\n";

	
		i := !i + 1;
	done;
	

	Printf.fprintf oc "\n};";

	close_out oc;
	()

(*
######
# output slab info table
######

open($fh, '>', $g_outputfile_slabinfotable) or die "Could not open file '$g_outputfile_slabinfotable' $!";

print $fh "\n/* autogenerated XMHF/GEEC sentinel slab info table */";
print $fh "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
print $fh "\n";
print $fh "\n";
print $fh "\n__attribute__(( section(\".data\") )) __attribute__((aligned(4096))) xmhfgeec_slab_info_t xmhfgeec_slab_info_table[] = {";


$i = 0;
while( $i < $g_totalslabs ){
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


    #slab_tos
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
    print $fh "\n	    {";
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

##done

	$i++;
}

print $fh "\n};";

close $fh;


######
*)


	
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

	umf_configure_slabs ();

	umf_output_infotable ();
	
	Self.result "Done.\n";
	()


let () = Db.Main.extend run

