(* frama-c coding conformance plugin *)
(* author: amit vasudevan (amitvasudevan@acm.org) *)
(* load using frama-c -load-script uccf.ml *)

open Cil_types


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

(*
let main () =
	let do_function f =
        if (Kernel_function.is_definition f) then
        	let fundec = Kernel_function.get_definition f in
  				let loc = Cil_datatype.Location.unknown in
  					let global = Cil_types.GFun (fundec, loc) in
  						Format.printf "%a" Printer.pp_global global
        	
        	(*
        		Format.printf "  %a:\n    fonction definition %a@."
            	Printer.pp_location (Kernel_function.get_location f)
            	Kernel_function.pretty f
			*)

		in Globals.Functions.iter do_function

let () = Db.Main.extend main
*)



(* print CFG by parsing AST *)

let print_stmt out = function
  | Instr i -> Printer.pp_instr out i
  | Return _ -> Format.pp_print_string out "<return>"
  | Goto _ -> Format.pp_print_string out "<goto>"
  | Break _ -> Format.pp_print_string out "<break>"
  | Continue _ -> Format.pp_print_string out "<continue>"
  | If (e,_,_,_) -> Format.fprintf out "if %a" Printer.pp_exp e
  | Switch (e,_,_,_) -> Format.fprintf out "switch %a" Printer.pp_exp e
  | Loop _ -> Format.fprintf out "<loop>"
  | Block _ -> Format.fprintf out "<block>"
  | UnspecifiedSequence _ -> Format.fprintf out "<unspecified sequence>"
  | TryFinally _ | TryExcept _  -> Format.fprintf out "<try>"
  | Throw (_,_) -> Format.fprintf out "<throw>"
  | TryCatch (_,_,_) -> Format.fprintf out "<trycatch>"
  

class print_cfg out = object
  inherit Visitor.frama_c_inplace

  method vfile _ =
    Format.fprintf out "@[<hov 2>digraph cfg {@ ";
    Cil.DoChildrenPost (fun f -> Format.fprintf out "}@]@."; f)

  method vglob_aux g =
    match g with
    | GFun(f,_) ->
        Format.fprintf out "@[<hov 2>subgraph cluster_%a {@ \
                           @[<hv 2>graph@ [label=\"%a\"];@]@ "
          Printer.pp_varinfo f.svar
          Printer.pp_varinfo f.svar;
        Cil.DoChildrenPost(fun g -> Format.fprintf out "}@]@ "; g)
    | _ -> Cil.SkipChildren

  method vstmt_aux s =
    Format.fprintf out "@[<hov 2>s%d@[[label=\"%a\"]@];@ "
      s.sid print_stmt s.skind;
    List.iter
      (fun succ -> Format.fprintf out "@[s%d -> s%d;@]@ " s.sid succ.sid)
      s.succs;
    Format.fprintf out "@]";
    Cil.DoChildren
end

let run () =
  let chan = open_out "cfg.out" in
  let fmt = Format.formatter_of_out_channel chan in
  Visitor.visitFramacFileSameGlobals (new print_cfg fmt) (Ast.get ());
  close_out chan

let () = Db.Main.extend run








