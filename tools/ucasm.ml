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

    		
let ucasm_process () =
    ()
    		
    		
    		
let run () =
	Self.result "Starting CASM extraction...\n";
	ucasm_process ();
	Self.result "Done.\n";
	()

let () = Db.Main.extend run





