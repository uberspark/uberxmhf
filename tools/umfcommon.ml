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
let g_maxincldevlistentries = ref 0;; 
let g_maxexcldevlistentries = ref 0;; 
let g_maxmemoffsetentries = ref 0;;


let slab_idtodir = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtogsm = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtommapfile = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtoname = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtotype = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtosubtype = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_nametoid = ((Hashtbl.create 32) : ((string,int)  Hashtbl.t));;
let slab_idtouapifnmask = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtomemoffsets = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;

let slab_idtomemgrantreadcaps =  ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtomemgrantwritecaps =  ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;

let slab_idtodatasize =  ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtocodesize =  ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtostacksize =  ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtodmadatasize =  ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;


let uapi_fnccomppre = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;
let uapi_fnccompasserts = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;
let uapi_fndef  = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;
let uapi_fndrvcode  = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;



let slab_idtordinclentries = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtordexclentries = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtordinclcount = ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtordexclcount = ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtomemoffsetstring = ((Hashtbl.create 32) : ((int,string)  Hashtbl.t));;
let slab_idtocallmask = ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;
let slab_idtocalleemask = ((Hashtbl.create 32) : ((int,int)  Hashtbl.t));;

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
	

(* parses a gsm file and populates relevant global structures *)	
let umfcommon_parse_gsm filename slabid totalslabs is_memoffsets = 
	let i = ref 0 in
    let j = ref 0 in
    let slab_rdinclcount = ref 0 in
    let slab_rdexclcount = ref 0 in
    let slab_rdinclentriesstring = ref "" in
    let slab_rdexclentriesstring = ref "" in
    let slab_uapifnmaskstring = ref "" in
    let slab_memoffsetsstring = ref "" in
    let slab_memoffsetcount = ref 0 in
    let uapi_key = ref "" in
    let slab_idtouapifnmask = ((Hashtbl.create 32) : ((int,int)  Hashtbl.t)) in
	let trimfilename = trim filename in
	let trimline = ref "" in
	let sfh = open_in trimfilename in
	let mftag = ref "" in
		
		slab_rdinclentriesstring := !slab_rdinclentriesstring ^ "{ \n";
    	slab_rdexclentriesstring := !slab_rdexclentriesstring ^ "{ \n";
		
		Format.printf "filename:%s\n" filename;
		Format.printf "slabid:%d\n" slabid;
		Format.printf "totalslabs:%d\n" totalslabs;
		Format.printf "is_memoffsets:%b\n" is_memoffsets;

		try
    		while true do
      			trimline := trim (input_line sfh);
				let lineentry = Str.split (Str.regexp ":") !trimline in
					if (List.length lineentry) > 0 then
						begin
							mftag := (trim (List.nth lineentry 0));
							
							if (compare "S" !mftag) = 0 then
								begin
						            (* lineentry[1] = name of destination slab that this slab calls *)
						            let tag_s_destslabname = (trim (List.nth lineentry 1)) in
						            let tag_s_mask = ref 0 in

							            Format.printf " mftag=%s, destslabname=%s, id=%d\n" !mftag tag_s_destslabname (Hashtbl.find slab_nametoid tag_s_destslabname);
						            	
						            	if (Hashtbl.mem slab_idtocallmask (Hashtbl.find slab_nametoid tag_s_destslabname)) then
						            		begin
						            			tag_s_mask := Hashtbl.find slab_idtocallmask (Hashtbl.find slab_nametoid tag_s_destslabname);
						            			tag_s_mask := !tag_s_mask lor (1 lsl slabid);
						            			Hashtbl.add slab_idtocallmask (Hashtbl.find slab_nametoid tag_s_destslabname) !tag_s_mask;
						            		end
						            	else
						            		begin
						            			tag_s_mask := (1 lsl slabid);
						            			Hashtbl.add slab_idtocallmask (Hashtbl.find slab_nametoid tag_s_destslabname) !tag_s_mask;
						            		end
						            	;
						            
						            	if (Hashtbl.mem slab_idtocalleemask slabid) then
						            		begin
						            			tag_s_mask := Hashtbl.find slab_idtocalleemask slabid;
						            			tag_s_mask := !tag_s_mask lor (1 lsl (Hashtbl.find slab_nametoid tag_s_destslabname));
						            			Hashtbl.add slab_idtocalleemask slabid !tag_s_mask;
						            		end
						            	else
						            		begin
						            			tag_s_mask := (1 lsl (Hashtbl.find slab_nametoid tag_s_destslabname));
						            			Hashtbl.add slab_idtocalleemask slabid !tag_s_mask;
						            		end
						            	;
	
								end

							else if (compare "U" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
									(* lineentry[1] = destination slab name, lineentry[2] = uapifn *)
									(* lineentry[3] = uapi fn composition pre-condition setup *)
									(* lineentry[4] = uapi fn composition check assertion *)
									let tag_u_destslabname = (trim (List.nth lineentry 1)) in
									let tag_u_destslabid = (Hashtbl.find slab_nametoid tag_u_destslabname) in
									let tag_u_uapifn = int_of_string (trim (List.nth lineentry 2)) in
									let tag_u_uapifnpre = (trim (List.nth lineentry 3)) in
									let tag_u_uapifncheckassert = (trim (List.nth lineentry 4)) in
									let tag_u_mask = ref 0 in
									let tag_u_uapikey = ref "" in
									let tag_u_tempstr = ref "" in
																		
										if (Hashtbl.mem slab_idtouapifnmask tag_u_destslabid) then
											begin
											tag_u_mask := Hashtbl.find slab_idtouapifnmask tag_u_destslabid; 
											tag_u_mask := !tag_u_mask lor (1 lsl tag_u_uapifn);
											Hashtbl.add slab_idtouapifnmask tag_u_destslabid !tag_u_mask;
											end
										else
											begin
											tag_u_mask := (1 lsl tag_u_uapifn);
											Hashtbl.add slab_idtouapifnmask tag_u_destslabid !tag_u_mask;
											end
										;

										(* make key *)
										tag_u_uapikey := tag_u_destslabname ^ "_" ^ (trim (List.nth lineentry 2));
										Format.printf "uapi key = %s\n" !tag_u_uapikey;
										if (Hashtbl.mem uapi_fnccomppre !tag_u_uapikey) then
											begin
											tag_u_tempstr := (Hashtbl.find uapi_fnccomppre !tag_u_uapikey);
											Hashtbl.add uapi_fnccomppre !tag_u_uapikey (!tag_u_tempstr ^ (Printf.sprintf "/* %s:*/\r\n" (Hashtbl.find slab_idtoname slabid)) ^ tag_u_uapifnpre ^ "\r\n");
											end
										else
											begin
											Hashtbl.add uapi_fnccomppre !tag_u_uapikey ( (Printf.sprintf "/* %s:*/\r\n" (Hashtbl.find slab_idtoname slabid)) ^ tag_u_uapifnpre ^ "\r\n");
											end
										;

										Format.printf "uapi fnccomppre =%s\n" (Hashtbl.find uapi_fnccomppre !tag_u_uapikey);

										if (Hashtbl.mem uapi_fnccompasserts !tag_u_uapikey) then
											begin
											tag_u_tempstr := (Hashtbl.find uapi_fnccompasserts !tag_u_uapikey);
											Hashtbl.add uapi_fnccompasserts !tag_u_uapikey (!tag_u_tempstr ^ (Printf.sprintf "/*@assert %s: " (Hashtbl.find slab_idtoname slabid)) ^ tag_u_uapifncheckassert ^ ";*/\r\n");
											end
										else
											begin
											Hashtbl.add uapi_fnccompasserts !tag_u_uapikey ((Printf.sprintf "/*@assert %s: " (Hashtbl.find slab_idtoname slabid)) ^ tag_u_uapifncheckassert ^ ";*/\r\n");
											end
										;

										Format.printf "uapi fnccompasserts =%s\n" (Hashtbl.find uapi_fnccompasserts !tag_u_uapikey);

								end

							else if (compare "RD" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
						            (* lineentry[1]=INCL or EXCL, lineentry[2] = vendor_id, *) 
						            (* lineentry[3] = device_id *)
						            let tag_rd_qual =  (trim (List.nth lineentry 1)) in
						            let tag_rd_vid =  (trim (List.nth lineentry 2)) in
						            let tag_rd_did =  (trim (List.nth lineentry 3)) in 
            
            						if (compare tag_rd_qual "INCL") = 0 then 
            							begin

							                if (!slab_rdinclcount >= !g_maxincldevlistentries) then 
							                	begin
							                		Format.printf "Error: Too many RD INCL entries (max=%d)\n" !g_maxincldevlistentries;
								                    ignore(exit 1);
							                	end
							                ;
							                
							                slab_rdinclentriesstring := !slab_rdinclentriesstring ^ "\t{ .vendor_id= " ^ tag_rd_vid ^ ", .device_id= " ^ tag_rd_did ^ " },\n";
							                slab_rdinclcount := !slab_rdinclcount + 1;
											            							
            							end
            						else if (compare tag_rd_qual "EXCL") = 0  then
            							begin

							                if (!slab_rdexclcount >= !g_maxexcldevlistentries) then
							                	begin
							                    	Format.printf "Error: Too many RD EXCL entries (max=%d)\n" !g_maxexcldevlistentries;
							                    	ignore (exit 1);
							                    end
							                ;

							                slab_rdexclentriesstring := !slab_rdexclentriesstring ^ "\t{ .vendor_id= " ^ tag_rd_vid ^ ", .device_id= " ^ tag_rd_did ^ " },\n";
							                slab_rdexclcount := !slab_rdexclcount + 1;
											            							
            							end
            						else
            							begin
            								Format.printf "Error: Illegal RD entry qualifier: %s\n" tag_rd_qual;
            								ignore(exit 1);
            							end
            						;
            							
								end

							else if (compare "RM" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
						            (* lineentry[1]=READ or WRITE, lineentry[2] = slabname *)
						            let tag_rm_qual =  (trim (List.nth lineentry 1)) in
						            let tag_rm_slabname =  (trim (List.nth lineentry 2)) in
            						let tag_rm_mask = ref 0 in
            
            						if (compare tag_rm_qual "READ") = 0 then 
            							begin
							                if (Hashtbl.mem slab_idtomemgrantreadcaps slabid) then
							                	begin
								                    tag_rm_mask := Hashtbl.find slab_idtomemgrantreadcaps slabid; 
								                    tag_rm_mask := !tag_rm_mask lor (1 lsl (Hashtbl.find slab_nametoid tag_rm_slabname));
								                    Hashtbl.add slab_idtomemgrantreadcaps slabid !tag_rm_mask;
							                	end
							                else
							                	begin
								                    tag_rm_mask := (1 lsl (Hashtbl.find slab_nametoid tag_rm_slabname));
								                    Hashtbl.add slab_idtomemgrantreadcaps slabid !tag_rm_mask;
							                	end
							                ;
            							end
            						else if (compare tag_rm_qual "WRITE") = 0 then
            							begin
							                if (Hashtbl.mem slab_idtomemgrantwritecaps slabid) then
							                	begin
								                    tag_rm_mask := Hashtbl.find slab_idtomemgrantwritecaps slabid; 
								                    tag_rm_mask := !tag_rm_mask lor (1 lsl (Hashtbl.find slab_nametoid tag_rm_slabname));
								                    Hashtbl.add slab_idtomemgrantwritecaps slabid !tag_rm_mask;
							                	end
							                else
							                	begin
								                    tag_rm_mask := (1 lsl (Hashtbl.find slab_nametoid tag_rm_slabname));
								                    Hashtbl.add slab_idtomemgrantwritecaps slabid !tag_rm_mask;
							                	end
							                ;
            							end
            						else 
	           							begin
    						            	Format.printf "Error: Illegal RM entry qualifier: %s\n" tag_rm_qual;
							                ignore(exit 1);
            							end
            						;
            						

								end

							else if (compare "RC" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
								end

							else if (compare "MS" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
						            (* $lineentry[1]=DATA,CODE,STACK,DMADATA, $lineentry[2] = size in bytes *)
						            let tag_ms_qual =  (trim (List.nth lineentry 1)) in
						            let tag_ms_size =  int_of_string (trim (List.nth lineentry 2)) in
            
            						if (compare tag_ms_qual "DATA") = 0 then 
            							begin
							                Hashtbl.add slab_idtodatasize slabid tag_ms_size;
            							end
            						else if (compare tag_ms_qual "CODE") = 0 then
            							begin
	                						Hashtbl.add slab_idtocodesize slabid tag_ms_size;
            							end
            						else if (compare tag_ms_qual "STACK") = 0 then
            							begin
                							Hashtbl.add slab_idtostacksize slabid tag_ms_size;
            							end
            						else if (compare tag_ms_qual "DMADATA") = 0 then
            							begin
                							Hashtbl.add slab_idtodmadatasize slabid tag_ms_size;
            							end
            						else
            							begin
							                Format.printf "Error: Illegal MS entry qualifier: %s\n" tag_ms_qual;
							                ignore(exit 1);
            							end
            						;
								end

							else if (compare "EX" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
            						(* lineentry[1]=export variable name *)
            						let tag_ex_varname =  (trim (List.nth lineentry 1)) in
						            
							            (* if we are processing memoffsets, then lookup this variable address *)
							            if (is_memoffsets) then 
							            	begin
							                    if (Hashtbl.mem slab_idtomemoffsets ((string_of_int slabid) ^ "_" ^ tag_ex_varname) ) then
								                	begin
									                    if (!slab_memoffsetcount < !g_maxmemoffsetentries) then
									                    	begin
									                        	slab_memoffsetsstring := !slab_memoffsetsstring ^ "\t0x" ^ (Hashtbl.find slab_idtomemoffsets ((string_of_int slabid) ^ "_" ^ tag_ex_varname)) ^ ",\n";
									                        	slab_memoffsetcount := !slab_memoffsetcount + 1;
									                        end
									                    else
									                    	begin
									                        	Format.printf "Error: Max. EX entries exceeded!\n";
									                        	ignore(exit 1);
									                        end
									                    ;
									                    
								                	end
								                else
								                	begin
								                    	Format.printf "Error: No entry found for slab: %s, EX entry: %s!" (Hashtbl.find slab_idtoname slabid) tag_ex_varname;
								                    	ignore (exit 1);
								                	end
								                ;
							            	end
							            ;
						
								end

							else if (compare "UFN" !mftag) = 0 then
								begin
									Format.printf " mftag=%s\n" !mftag;
									(* lineentry[1]=uapi function id (numeric) *)
									(* lineentry[2]=uapi function definition (string) *)
									(* lineentry[3]=uapi function driver code (string) *)
									let tag_ufn_uapifnid =  (trim (List.nth lineentry 1)) in
									let tag_ufn_uapifndef =  (trim (List.nth lineentry 2)) in
									let tag_ufn_uapifndrvcode =  (trim (List.nth lineentry 3)) in
									let tag_ufn_uapikey = ref "" in
									
										(* uapi function definition tag, should only appear in uapi slabs *)
										if (compare (Hashtbl.find slab_idtosubtype slabid) "UAPI") = 0 then
											begin
												
												Format.printf "slab %s, found UFN tag \n" (Hashtbl.find slab_idtoname slabid);
												(* make key *)
												tag_ufn_uapikey := (Hashtbl.find slab_idtoname slabid) ^ "_" ^ tag_ufn_uapifnid;
												Format.printf "uapi key = %s \n" !tag_ufn_uapikey;
												Format.printf "uapi fndef = %s \n" tag_ufn_uapifndef;
												Format.printf "uapi fndrvcode = %s \n" tag_ufn_uapifndrvcode;
									
									            Hashtbl.add uapi_fndef !tag_ufn_uapikey tag_ufn_uapifndef; (* store uapi function definition indexed by uapi_key *)
									            Hashtbl.add uapi_fndrvcode !tag_ufn_uapikey tag_ufn_uapifndrvcode; (* store uapi function driver code by uapi_key *)

											end
										else
											begin
												Format.printf "Error: Illegal UFN tag; slab is not a uapi slab!\n";
                        						ignore(exit 1);
											end
										;
									
								end



							else
								begin
								end
							;
							      			
						end

					else
						begin
						end
					;
					
					i := !i + 1;
		    done;
		with End_of_file -> 
    			close_in sfh;
    	;		
	
    	if !slab_rdinclcount = 0 then
    		begin
        		slab_rdinclentriesstring := !slab_rdinclentriesstring ^ "0 \n}, \n";
    		end
    	else
    		begin
        		slab_rdinclentriesstring := !slab_rdinclentriesstring ^ "}, \n";
    		end
    	;
    	
    	if !slab_rdexclcount = 0 then
    		begin
        		slab_rdexclentriesstring := !slab_rdexclentriesstring ^ "0 \n}, \n";
    		end
    	else	
    		begin
        		slab_rdexclentriesstring := !slab_rdexclentriesstring ^ "}, \n";
    		end
    	;

    	Hashtbl.add slab_idtordinclentries slabid !slab_rdinclentriesstring;
    	Hashtbl.add slab_idtordexclentries slabid !slab_rdexclentriesstring;
    	Hashtbl.add slab_idtordinclcount slabid !slab_rdinclcount;
    	Hashtbl.add slab_idtordexclcount slabid !slab_rdexclcount;

    	while !j < totalslabs do
    		begin
        		if (Hashtbl.mem slab_idtouapifnmask !j) then
        			begin
        				slab_uapifnmaskstring := !slab_uapifnmaskstring ^ (Printf.sprintf "\t0x%08x,\n" (Hashtbl.find slab_idtouapifnmask !j));
        			end
        		else
        			begin
						slab_uapifnmaskstring := "0x00000000";        			
        			end
        		;
        		j := !j + 1;
    		end
    	done;


		(* if we are processing memoffsets, then store memoffsets string indexed by slabid *)
    	if is_memoffsets then 
        	begin
        		if (compare !slab_memoffsetsstring "") = 0 then 
        			begin
            			Hashtbl.add slab_idtomemoffsetstring slabid "0";
            		end
            	else
            		begin
	            		Hashtbl.add slab_idtomemoffsetstring slabid !slab_memoffsetsstring;
    				end
    			;    	
        	end
    	;

	(*return value*)
	!slab_uapifnmaskstring




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
				    slabgsmfile := g_rootdir ^ !slabdir ^ "/" ^ !slabname ^ ".gsm.pp";
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
			
				if (g_memoffsets && ((compare (Hashtbl.find slab_idtosubtype !i) "XRICHGUEST") <> 0) ) then
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





