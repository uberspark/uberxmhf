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

module Cmdopt_uobjconfigurescript = Self.String
	(struct
		let option_name = "-umf-uobjconfigurescript"
		let default = ""
		let arg_name = "uobjconfigurescript"
		let help = "uobj configuration script"
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
let g_uobjconfigurescript = ref "";; (* argv 1 *)
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
	g_uobjconfigurescript := Cmdopt_uobjconfigurescript.get();
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
	Self.result "g_uobjconfigscript=%s\n" !g_uobjconfigurescript;
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
	    if ((compare (Hashtbl.find slab_idtosubtype !i) "XRICHGUEST") <> 0) then
	    	begin
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
			end	
	    else
	    	begin
			    Hashtbl.add slab_idtocode_addrstart !i (Printf.sprintf "0x%08x" (Hashtbl.find slab_idtocodesize !i));
			    Hashtbl.add slab_idtocode_addrend !i (Printf.sprintf "0x%08x" (Hashtbl.find slab_idtodatasize !i));
			
			    Hashtbl.add slab_idtodata_addrstart !i (Printf.sprintf "0x%08x" (Hashtbl.find slab_idtostacksize !i));
			    Hashtbl.add slab_idtodata_addrend !i (Printf.sprintf "0x%08x" (Hashtbl.find slab_idtodmadatasize !i));
			
			    Hashtbl.add slab_idtostack_addrstart !i (Printf.sprintf "0x%08x" 0);
			    Hashtbl.add slab_idtostack_addrend !i (Printf.sprintf "0x%08x" 0);
			
			    Hashtbl.add slab_idtodmadata_addrstart !i (Printf.sprintf "0x%08x" 0);
			    Hashtbl.add slab_idtodmadata_addrend !i (Printf.sprintf "0x%08x" 0);
			end	    	
	    ;
		

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
		        l_cmdline := 	(Printf.sprintf "cd %s%s && %s " !g_rootdir (Hashtbl.find slab_idtodir !i) !g_uobjconfigurescript) ^
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
	Printf.fprintf oc "\n#include <xmhf.h>";
	Printf.fprintf oc "\n#include <xmhfgeec.h>";
	Printf.fprintf oc "\n#include <xmhf-debug.h>";
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
	    if (!g_memoffsets && ((compare (Hashtbl.find slab_idtosubtype !i) "XRICHGUEST") <> 0) ) then
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


let umf_output_linkerscript () =
    let oc = open_out !g_outputfile_linkerscript in

	Printf.fprintf oc "\n/* autogenerated XMHF linker script */";
	Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
	
	Printf.fprintf oc "\n#include <xmhf.h>";
	Printf.fprintf oc "\n";
	Printf.fprintf oc "\n";
	Printf.fprintf oc "\nOUTPUT_ARCH(\"i386\")";
	Printf.fprintf oc "\n";
	Printf.fprintf oc "\nMEMORY";
	Printf.fprintf oc "\n{";
	Printf.fprintf oc "\n  all (rwxai) : ORIGIN = 0x%08x, LENGTH = 0x%08x" !g_loadaddr !g_loadmaxsize;
	Printf.fprintf oc "\n  unaccounted (rwxai) : ORIGIN = 0, LENGTH = 0 /* see section .unaccounted at end */";
	Printf.fprintf oc "\n}";
	Printf.fprintf oc "\nSECTIONS";
	Printf.fprintf oc "\n{";
	Printf.fprintf oc "\n	. = 0x%08x;" !g_loadaddr;
	Printf.fprintf oc "\n";


	i := 0;
	while (!i < !g_totalslabs) do

	    if ( (compare (Hashtbl.find slab_idtosubtype !i) "XRICHGUEST") <> 0 ) then
	    	begin
			    Printf.fprintf oc "\n	.slab_%s : {" (Hashtbl.find slab_idtoname !i);
			    Printf.fprintf oc "\n		. = ALIGN(1);";
			    Printf.fprintf oc "\n		_objs_slab_%s/%s.slo(.slabcode)" (Hashtbl.find slab_idtoname !i) (Hashtbl.find slab_idtoname !i);
			    Printf.fprintf oc "\n		. = ALIGN(1);";
			    Printf.fprintf oc "\n		_objs_slab_%s/%s.slo(.slabdata)" (Hashtbl.find slab_idtoname !i) (Hashtbl.find slab_idtoname !i);
			    Printf.fprintf oc "\n		. = ALIGN(1);";
			    Printf.fprintf oc "\n		_objs_slab_%s/%s.slo(.slabstack)" (Hashtbl.find slab_idtoname !i) (Hashtbl.find slab_idtoname !i);
			    Printf.fprintf oc "\n		. = ALIGN(1);";
			    Printf.fprintf oc "\n		_objs_slab_%s/%s.slo(.slabdmadata)" (Hashtbl.find slab_idtoname !i) (Hashtbl.find slab_idtoname !i);
			    Printf.fprintf oc "\n		. = ALIGN(1);";
			    Printf.fprintf oc "\n	} >all=0x0000";
			    Printf.fprintf oc "\n";
			end
		;		
		
	    i := !i + 1;
	done;

	Printf.fprintf oc "\n";
	Printf.fprintf oc "\n	/* this is to cause the link to fail if there is";
	Printf.fprintf oc "\n	* anything we didn't explicitly place.";
	Printf.fprintf oc "\n	* when this does cause link to fail, temporarily comment";
	Printf.fprintf oc "\n	* this part out to see what sections end up in the output";
	Printf.fprintf oc "\n	* which are not handled above, and handle them.";
	Printf.fprintf oc "\n	*/";
	Printf.fprintf oc "\n	.unaccounted : {";
	Printf.fprintf oc "\n	*(*)";
	Printf.fprintf oc "\n	} >unaccounted";
	Printf.fprintf oc "\n}";
	Printf.fprintf oc "\n";


	close_out oc;
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

	umf_configure_slabs ();

	umf_output_infotable ();
	
	umf_output_linkerscript ();
	
	Self.result "Done.\n";
	()


let () = Db.Main.extend run

