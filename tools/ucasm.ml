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


let ucasm_file_out = "ucasm.out";;
let ucasm_file_in = "ucasm.in";;
    		
let ucasm_process () =
    let ic = open_in ucasm_file_in in
    let oc = open_out ucasm_file_out in
    let tline = ref "" in	
    	
		try
    		while true do
      			tline := (input_line ic);
      			Printf.printf " %s\n" !tline;
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





