(* frama-c coding conformance plugin *)
(* author: amit vasudevan (amitvasudevan@acm.org) *)
(* load using frama-c -load-script uccf.ml *)

open Cil_types


module Self = Plugin.Register
	(struct
		let name = "US Coding Conformance"
		let shortname = "uccf"
		let help = "UberSpark coding conformance check plugin"
	end)

module CmdoptDisallowFp = Self.False
	(struct
		let option_name = "-uccf-disallowfp"
		let default = false
		let help = "when on (off by default), disallow function pointer invocations"
	end)


(* ------------------------------------------------------------------------ *)
(* hello world output to a file *)
(*
let run () =
	let chan = open_out "hello.out" in
		Printf . fprintf chan "Hello, world!\n";
		close_out chan

let () = Db.Main.extend run
*)

(* ------------------------------------------------------------------------ *)
(* parse all global variables and categorize into defined vs declared *)
(*
let do_var v _init =
      Self.result "Global variable %a (%s)@." Cil_datatype.Varinfo.pretty v
        (if v.Cil_types.vdefined then "defined" else "declared")

let () = Db.Main.extend (fun () -> Globals.Vars.iter do_var)
*)


(* ------------------------------------------------------------------------ *)
(* parse all functions and categorize into defined vs declared *)
(*
let main () =
	let do_function f =
        Self.result "  %a:\n    fonction %a (%s)@."
            Printer.pp_location (Kernel_function.get_location f)
            Kernel_function.pretty f
            (if (Kernel_function.is_definition f) then "defined" else "declared")
		in Globals.Functions.iter do_function

let () = Db.Main.extend main
*)


(* ------------------------------------------------------------------------ *)
(* parse only defined functions *)

(*
let main () =
	let do_function f =
        if (Kernel_function.is_definition f) then
        	let fundec = Kernel_function.get_definition f in
  				let loc = Cil_datatype.Location.unknown in
  					let global = Cil_types.GFun (fundec, loc) in
  						Self.result "%a" Printer.pp_global global
        	
        	(*
        		Self.result "  %a:\n    fonction definition %a@."
            	Printer.pp_location (Kernel_function.get_location f)
            	Kernel_function.pretty f
			*)

		in Globals.Functions.iter do_function

let () = Db.Main.extend main
*)



(* ------------------------------------------------------------------------ *)
(* print CFG by parsing AST *)

(*
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
*)


(* ------------------------------------------------------------------------ *)
(* dump entire AST *)

(* les methodes de cette classe sont utilisées pour faire du debug *)
class shared = object (self)

	method private process_call lv e el l = 
		"call [" ^ (self#print_opt_lval lv) ^ "] [" ^ (self#print_expr e) ^ "] [" ^ (self#print_expr_list el) ^ "] [" ^ (self#print_location l) ^ "]"

    method private process_varinfo v = 
    	v.vname ^ " " ^ (self#print_type v.vtype)





    method private print_position pos = "(" ^ pos.Lexing.pos_fname ^ " " ^ (string_of_int pos.Lexing.pos_lnum) ^ " " ^ (string_of_int pos.Lexing.pos_bol) ^ " " ^ (string_of_int pos.Lexing.pos_cnum) ^ ")"

(*
    method private print_location (pos_a, pos_b) = "[" ^ (self#print_position pos_a) ^ "," ^ (self#print_position pos_b) ^ "]"
*)
  method private print_location (_, _) = ""

  method private print_type t = match t with
      | TVoid _ -> "void"
      | TInt _ -> "int"
      | TFloat _ -> "float"
      | TPtr _ -> "ptr"
      | TArray _ -> "array"
      | TFun _ -> "fun"
      | TNamed _ -> "named"
      | TComp _ -> "comp"
      | TEnum _ -> "enum"
      | TBuiltin_va_list _ -> "buildin_va_list"

    method private print_varinfo v = (self#process_varinfo v)

    method private print_varinfo_list vl = 
      let rec print_varinfo_list_aux vlaux accu first = match vlaux with
        | [] -> accu ^ "]"
        | h::t -> print_varinfo_list_aux t (accu ^ (if first then "" else ",") ^ (self#print_varinfo h)) false
      in print_varinfo_list_aux vl "[" true

    method private print_fundec f = (self#print_varinfo f.svar) ^ " " ^ (self#print_varinfo_list f.sformals)

    method private print_glob_fun (f, _) = (self#print_fundec f)

    method private print_lhost lh = match lh with
      | Var vi -> "var:[" ^ self#print_varinfo vi ^ "]"
      | Mem e -> "mem:[" ^ self#print_expr e ^ "]"

    method private is_lval_ptr (lh, _) = match lh with
      | Var _ -> false
      | Mem _ -> true

    method private print_offset o = match o with
      | NoOffset -> "nooffset"
      | Field _ -> "field"
      | Index (e,o) -> "index ("^ (self#print_expr e) ^ ")"

    (*
    method private print_offset _  = ""
	*)

    method private print_lval lv = let (lh, off) = lv in  "lval:[" ^ (self#print_lhost lh) ^ " " ^ (self#print_offset off) ^ "]"

    method private print_opt_lval olv = match olv with
      | None -> "none";
      | Some e -> (self#print_lval e);

    method private print_mem e = self#print_expr e
    
(*    method private print_varinfo v = *)

    method private print_unop u = match u with
      | Neg -> "-"
      | BNot -> "~"
      | LNot -> "!"

    method private print_binop b = match b with
     | PlusA -> "+"
     | PlusPI -> "p+i"
     | IndexPI -> "ip+i"
     | MinusA -> "-"
     | MinusPI -> "p-i"
     | MinusPP -> "ip-i"
     | Mult -> "*"
     | Div -> "/"
     | Mod -> "%"
     | Shiftlt -> "<<"
     | Shiftrt -> ">>"
     | Lt -> ">"
     | Gt -> ">"
     | Le -> "<="
     | Ge -> ">="
     | Eq -> "=="
     | Ne -> "!="
     | BAnd -> "&"
     | BXor -> "^"
     | BOr -> "|"
     | LAnd -> "&&"
     | LOr -> "||"

    method private print_caste (t, e) = "[cast (" ^ (self#print_type t) ^ ") ( " ^ (self#print_expr e) ^ ")]"


    method private is_expr_enode_lval expr = match expr.enode with
      | Lval lv -> true
      |_ -> false
      

    method private print_expr_aux expr = match expr.enode with
      | Const _ -> "const"
      | Lval lv -> (self#print_lval lv)
      | SizeOf t -> "sizeof(" ^ (self#print_type t) ^ ")"
      | SizeOfE e -> "sizeof(" ^ (self#print_expr e) ^ ")"
      | SizeOfStr s -> "sizeof(" ^ s ^ ")"
      | AlignOf t -> "__alignof_(" ^ (self#print_type t) ^ ")"
      | AlignOfE e -> "__alignof_(" ^ (self#print_expr e) ^ ")"
      | UnOp (u, e, t) -> "unop([" ^ (self#print_unop u) ^ "," ^ (self#print_expr e) ^ "]:" ^ (self#print_type t) ^ ")"
      | BinOp (b, e1, e2, t) -> "binop([" ^ (self#print_binop b) ^ "," ^ (self#print_expr e1) ^ "," ^ (self#print_expr e2) ^ "]:" ^ (self#print_type t) ^ ")"
      | CastE (t, e) -> self#print_caste (t, e)
      | AddrOf lv -> "addrof(" ^ (self#print_lval lv) ^ ")"
      | StartOf lv -> "addrof(" ^ (self#print_lval lv) ^ ")"
      | Info (e, _) -> "info("^ (self#print_expr e) ^ ")"

    method private print_expr expr = "expr:[" ^ (self#print_expr_aux expr) ^ "]"

    method private print_opt_exp exp = match exp with
      | None -> "none";
      | Some e -> (self#print_expr e);

    method private print_expr_list exprl = 
      let rec print_expr_list_aux exprlaux accu first = match exprlaux with
        | [] -> accu ^ "]"
        | h::t -> print_expr_list_aux t (accu ^ (if first then "" else ",") ^ (self#print_expr h)) false
      in print_expr_list_aux exprl "[" true



   method private print_instr instr = match instr with 
      | Set (lv, e, loc) -> "set[" ^ (self#print_lval lv) ^ "," ^ (self#print_expr e) ^ (self#print_location loc) ^ "]"
      (*
      | Call (lv, e, el, l) -> "call [" ^ (self#print_opt_lval lv) ^ "] [" ^ (self#print_expr e) ^ "] [" ^ (self#print_expr_list el) ^ "] [" ^ (self#print_location l) ^ "]"
      *)
      | Call (lv, e, el, l) -> self#process_call lv e el l
      | Asm _ -> "asm"
      | Skip l -> "skip " ^ (self#print_location l)
      | Code_annot _ -> "code annot"

    method private print_goto _ = "goto"

    method private print_break b = self#print_location b

    method private print_continue c = self#print_location c

    method private print_if (e, _, _, l) = (self#print_expr e) ^ (self#print_location l)
end



let print_ast () =
    let print_visitor = object (self)
    (* visit the AST in place by inheritance *)
      inherit shared 
      inherit Visitor.frama_c_inplace

	    method private process_varinfo v = 
    		let varname_regexp = Str.regexp "xmhfhwm_" in
    		let is_hwmvar = ref false in
    			is_hwmvar := (Str.string_match varname_regexp v.vname 0); 
    			if !is_hwmvar then
    				begin
		    			"HWM name->" ^ v.vname ^ ", type->" ^ (self#print_type v.vtype);
    				end
    			else
    				begin
    					"name->" ^ v.vname ^ ", type->" ^ (self#print_type v.vtype);
    				end
    			; 



		method private process_call lv e el l = 
			let is_funcptr = ref false in 
			let is_expr_enode_lval = ref false in

		
				match e.enode with
			      | Lval lvv	->	(
			      		      			let (lvv_lh, lvv_off) = lvv in  
			      		      				match lvv_lh with
      											| Var lvv_lh_vi	->	(
      																	"ocall [" ^ (self#print_opt_lval lv) ^ "] [" ^ (self#print_expr e) ^ "] [" ^ (self#print_expr_list el) ^ "] [" ^ (self#print_location l) ^ "]" ;
      																)
      											|_ 				-> 	(
																		if CmdoptDisallowFp.get() then 
																			begin
																				is_funcptr := true;
																				Self.result "\nError: Function pointer invocation detected\n";
																				ignore(exit 1);
			      															"";
			      															end
			      														else
			      															begin
																				"ocall [" ^ (self#print_opt_lval lv) ^ "] [" ^ (self#print_expr e) ^ "] [" ^ (self#print_expr_list el) ^ "] [" ^ (self#print_location l) ^ "]" ;			      															
			      															end
			      														;
      																)
			      		      				;
			    					)
			      |_ 			-> 	(
										if CmdoptDisallowFp.get() then 
											begin
												is_funcptr := true;
												Self.result "\nError: Function pointer invocation detected\n";
												ignore(exit 1);
											"";
											end
										else
											begin
												"ocall [" ^ (self#print_opt_lval lv) ^ "] [" ^ (self#print_expr e) ^ "] [" ^ (self#print_expr_list el) ^ "] [" ^ (self#print_location l) ^ "]" ;			      															
											end
										;
			      					)
      			;

     
				
			
		method private dump_varinfo (v:Cil_types.varinfo) =
			Self.result "\n   %s" (self#print_varinfo v);
			()

	  method vglob_aux s =
	    match s with
	    | GFun(f,_) ->
	    	(
		        Self.result "\n function [%s] {"  (self#print_varinfo f.svar);	          
	
				Self.result "\n  formals:";
			    List.iter self#dump_varinfo f.sformals;
				Self.result "\n  local vars:";
			    List.iter self#dump_varinfo f.slocals;
	
		        
		        Cil.DoChildrenPost(fun s -> Self.result "\n }@ "; s)
	    	)
	    
	    | GVar (v, inito, l) ->
	    	(
	    		Self.result "\n global var def [%s]"  (self#print_varinfo v);

		        Cil.DoChildrenPost(fun s -> Self.result "\n @ "; s)
	    	)
	    		    	
	    | _ -> Cil.SkipChildren

      
      method vstmt_aux s = match s.skind with
      | Instr i -> Self.result "\n instr %s" (self#print_instr i); Cil.DoChildren
      | Return (eo, _) -> Self.result "\n return %s" (self#print_opt_exp eo); Cil.DoChildren
      | Goto _ -> Self.result "\n goto"; Cil.DoChildren
      | Break _ -> Self.result "\n break"; Cil.DoChildren
      | Continue _ -> Self.result "\n %s" "continue"; Cil.DoChildren
      | If (e, b1, b2, l) -> Self.result "\n %s" (self#print_if (e, b1, b2, l)); Cil.DoChildren
      | Switch _ -> Self.result "\n %s" "switch"; Cil.DoChildren
      | Loop _ -> Self.result "\n loop"; Cil.DoChildren
      | Block _ -> Self.result "\n block"; Cil.DoChildren
      | UnspecifiedSequence _ -> Self.result "\n unspecified sequence"; Cil.DoChildren
      | _ -> Self.result "\n other stmt"; Cil.DoChildren
    end
    in Visitor.visitFramacFile print_visitor (Ast.get ()) ;
    ()



    		
let run () =
	Self.result "Parsing source file AST...\n";
	print_ast ();
	Self.result "Done.\n";
	()

let () = Db.Main.extend run





