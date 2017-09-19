(* frama-c CASM instruction substitution plugin *)
(* author: amit vasudevan (amitvasudevan@acm.org) *)
(* load using frama-c -load-script ucasm.ml *)

open Cil_types

(*
	register plugin with frama-c
*)
module Self = Plugin.Register
	(struct
		let name = "US CASM"
		let shortname = "ucasm"
		let help = "UberSpark CASM instruction substitution plugin"
	end)


module CmdoptInputFile = Self.String
	(struct
		let option_name = "-ucasm-infile"
		let default = "ucasm.in"
		let arg_name = "input-file"
		let help = "CASM input file"
	end)

module CmdoptOutputFile = Self.String
	(struct
		let option_name = "-ucasm-outfile"
		let default = "ucasm.out"
		let arg_name = "output-file"
		let help = "CASM Assembly output file"
	end)


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
  
  		
let ucasm_process () =
	let infile = CmdoptInputFile.get() in
	let outfile = CmdoptOutputFile.get() in
    let ic = open_in infile in
    let oc = open_out outfile in
    let tline = ref "" in
    let outline = ref "" in	
    let annotline_regexp = Str.regexp "_ = annot " in
    		    	
		try
    		while true do
      			tline := trim (input_line ic);
      			if (Str.string_match annotline_regexp !tline 0) then
      				begin
		      			outline := (Str.string_after !tline 11);
		      			outline := Str.string_before !outline ((String.length !outline) - 3);
		      			Printf.fprintf oc "%s\n" !outline; 
      				end
      			else
      				begin
      				end
      			;
      			
		    done;
		with End_of_file -> 
    			close_in ic;
    	;		
    
    	close_out oc;
    ()
    		
    		
    		
let run () =
		Self.result "Starting CASM extraction...\n";
		ucasm_process ();
		Self.result "Done.\n";
		()

let () = Db.Main.extend run





