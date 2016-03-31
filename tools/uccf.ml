(* frama-c coding conformance plugin *)
(* author: amit vasudevan (amitvasudevan@acm.org) *)
(* load using frama-c -load-script uccf.ml *)

(* hello world output to a file *)
(*
let run () =
	let chan = open_out "hello.out" in
		Printf . fprintf chan "Hello, world!\n";
		close_out chan

let () = Db.Main.extend run
*)

(* parse all global variables and categorize into defined vs declared *)
(*
let do_var v _init =
      Format.printf "Global variable %a (%s)@." Cil_datatype.Varinfo.pretty v
        (if v.Cil_types.vdefined then "defined" else "declared")

let () = Db.Main.extend (fun () -> Globals.Vars.iter do_var)
*)


(* parse all functions and categorize into defined vs declared *)
(*
let main () =
	let do_function f =
        Format.printf "  %a:\n    fonction %a (%s)@."
            Printer.pp_location (Kernel_function.get_location f)
            Kernel_function.pretty f
            (if (Kernel_function.is_definition f) then "defined" else "declared")
		in Globals.Functions.iter do_function

let () = Db.Main.extend main
*)


(* parse only defined functions *)

let main () =
	let do_function f =
        if (Kernel_function.is_definition f) then
        	Format.printf "  %a:\n    fonction definition %a@."
            	Printer.pp_location (Kernel_function.get_location f)
            	Kernel_function.pretty f

		in Globals.Functions.iter do_function

let () = Db.Main.extend main






