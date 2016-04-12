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
let slab_idtouapifnmask = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtomemoffsets = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;


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


let umfcommon_parse_mmap filename slabid totalslabs =
	let i = ref 0 in
	let trimfilename = trim filename in
	let trimline = ref "" in
	let sfh = open_in trimfilename in
	let varname = ref "" in
	let varaddr = ref "" in
	
		Format.printf "slabid:%d\n" slabid;
		Format.printf "totalslabs:%d\n" totalslabs;
		Format.printf "filename:%s\n" trimfilename;

		try
    		while true do
      			trimline := trim (input_line sfh);
				let lineentry = Str.split (Str.regexp ":") !trimline in
					varname := (trim (List.nth lineentry 0));
					varaddr := (trim (List.nth lineentry 1));
					
					(* Format.printf "    varname=%s\n" !varname; *)      			
					(* Format.printf "    varaddr=%s\n" !varaddr; *)      			
			        Hashtbl.add slab_idtomemoffsets ((string_of_int slabid) ^ "_" ^ !varname) !varaddr;

					i := !i + 1;
		    done;
		with End_of_file -> 
    			close_in sfh;
    	;		

	()
	
	
let umfcommon_parse_gsm filename slabid totalslabs is_memoffsets = 
	Format.printf "filename:%s\n" filename;
	Format.printf "slabid:%d\n" slabid;
	Format.printf "totalslabs:%d\n" totalslabs;
	Format.printf "is_memoffsets:%b\n" is_memoffsets;
	""


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
						umfcommon_parse_mmap (Hashtbl.find slab_idtommapfile !i) !i !g_totalslabs;
						Hashtbl.add slab_idtouapifnmask !i (umfcommon_parse_gsm (Hashtbl.find slab_idtogsm !i) !i !g_totalslabs true);
					end
				else
					begin
						Hashtbl.add slab_idtouapifnmask !i (umfcommon_parse_gsm (Hashtbl.find slab_idtogsm !i) !i !g_totalslabs false);
					end
				;				    	

	    		i := !i + 1;
			end
		done;



		
	()





