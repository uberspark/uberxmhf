(* frama-c coding conformance plugin *)
(* author: amit vasudevan (amitvasudevan@acm.org) *)
(* load using frama-c -load-script uccf.ml *)

(*
let run () =
	let chan = open_out "hello.out" in
		Printf . fprintf chan "Hello, world!\n";
		close_out chan

let () = Db.Main.extend run
*)


let do_var v _init =
      Format.printf "Global variable %a (%s)@." Cil_datatype.Varinfo.pretty v
        (if v.Cil_types.vdefined then "defined" else "declared")

let () = Db.Main.extend (fun () -> Globals.Vars.iter do_var)
