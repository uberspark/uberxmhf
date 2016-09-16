(* frama-c hardware model embedding plugin *)
(* author: amit vasudevan (amitvasudevan@acm.org) *)
(* load using frama-c -load-script uhwm.ml *)

open Cil_types

(* register plugin with frama-c *)
module Self = Plugin.Register
	(struct
		let name = "US HWM Plugin"
		let shortname = "uccf"
		let help = "UberSpark hardware model embedding plugin"
	end)

(*
	option to check for function-pointer invocation 
*)
module CmdoptDisallowFp = Self.False
	(struct
		let option_name = "-uccf-disallowfp"
		let default = false
		let help = "when on (off by default), disallow function pointer invocations"
	end)




(* shared class for combing through AST nodes *)
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
      inherit shared 
      inherit Visitor.frama_c_inplace

	    method private process_varinfo v = 
    		let varname_regexp = Str.regexp "xmhfhwm_" in
    			begin
	    			Self.result "\nVarinfo found\n";
		        	Self.result "\n %a" Cil_printer.pp_varinfo v;
	    			"";
	    		end

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
	
		        (*
		        	let loc = Cil_datatype.Location.unknown in
  					let global = Cil_types.GFun (f, loc) in
  						Format.printf "%a" Printer.pp_global global;
		        *)
		        
		        Cil.DoChildrenPost(fun s -> Self.result "\n }@ "; s)
	    	)
	    
	    | GVar (v, inito, l) ->
	    	(
	    		Self.result "\n global var def [%s]"  (self#print_varinfo v);

				let global = Cil_types.GVar (v, inito, l) in
					Format.printf "%a" Printer.pp_global global;

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

let mkFunTyp (rt : typ) (args : (string * typ) list) : typ =
  TFun(rt, Some(List.map (fun a -> (fst a, snd a, [])) args), false, [])
  
(* embedding hwm AST visitor *)
class embed_hwm_visitor = object (self)
	inherit Visitor.frama_c_inplace

	val mutable hwm_is_casm_function: bool = false

	method private hwm_gen_call_stmt_for_function fname ftyp fexp_lst loc = 
		let fvar = Cil.findOrCreateFunc (Ast.get ()) fname ftyp in
		let instr = Cil_types.Call(None, Cil.evar ~loc:loc fvar, fexp_lst, loc) in
		let new_stmt = Cil.mkStmtOneInstr (instr) in
			new_stmt


	method private hwm_gen_stack_push_param_stmt e loc = 
		let ftyp = mkFunTyp Cil.voidType ["val", Cil.intType] in
		let fvname = "ci_pushl" in
		let fvar = Cil.findOrCreateFunc (Ast.get ()) fvname ftyp in
		let instr = Cil_types.Call(None, Cil.evar ~loc:loc fvar, [e], loc) in
		let new_stmt = Cil.mkStmtOneInstr (instr) in
			new_stmt


	method private hwm_gen_push_eip loc = 
		let new_stmt = self#hwm_gen_stack_push_param_stmt (Cil.integer ~loc 3735928559) loc in
			new_stmt


	method private hwm_gen_stack_pop_params_stmt_for_casm_function exp_lst loc = 
		let ftyp = mkFunTyp Cil.voidType ["val", Cil.intType] in
		let fvname = "ci_addl_esp" in
		let fvar = Cil.findOrCreateFunc (Ast.get ()) fvname ftyp in
		let instr = Cil_types.Call(None, Cil.evar ~loc:loc fvar, [(Cil.integer ~loc ((List.length exp_lst) * 4) )], loc) in
		let new_stmt = Cil.mkStmtOneInstr (instr) in
			new_stmt

	
	method private hwm_gen_return_result lval loc = 
		let var_edx = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_edx" Cil.uintType in
		let var_eax = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eax" Cil.uintType in
		let exp1 = Cil.new_exp ~loc (BinOp(Shiftlt, (Cil.evar ~loc:loc var_edx), (Cil.integer ~loc 32), (Cil.typeOfLval lval))) in
		let exp2 = Cil.new_exp ~loc (CastE((Cil.typeOfLval lval), exp1)) in
		let exp3 = Cil.new_exp ~loc (BinOp(BOr, exp2 ,(Cil.evar ~loc:loc var_eax), (Cil.typeOfLval lval))) in
		let instr = Cil_types.Set(lval, exp3, loc) in
		let new_stmt = Cil.mkStmtOneInstr (instr) in
			new_stmt

	
	method private hwm_gen_stack_push_param_stmts_for_casm_function exp_lst loc = 
		let stmts_list = ref [] in
		let rev_exp_lst = List.rev exp_lst in
			begin
				for i = 0 to ((List.length rev_exp_lst)-1) do
					begin
						Self.result "\nfor loop i=%d\n" i;
						(* Printer.pp_exp (Format.std_formatter) (List.nth rev_exp_lst i); *)
						stmts_list := List.append !stmts_list [(self#hwm_gen_stack_push_param_stmt (List.nth rev_exp_lst i) loc)] ;
						(* Printer.pp_stmt (Format.std_formatter) (self#hwm_gen_stack_push_param_stmt (List.nth rev_exp_lst i) loc);*)
					end
				done;			
			!stmts_list	
			end

			 
	method vstmt_aux s =
		Cil.ChangeDoChildrenPost(
			s,fun s -> (
				match s.skind with
				| Instr (Call(lval, exp, exp_lst, loc)) ->
				begin
	                match exp.enode with
	                | Lval(Var(var), _) ->
	                begin
						let hwm_stmt_list = ref [] in
										
						if (Str.string_match (Str.regexp "casm_") var.vname 0) then
							begin
								hwm_stmt_list := self#hwm_gen_stack_push_param_stmts_for_casm_function exp_lst loc;
                	            hwm_stmt_list := List.append !hwm_stmt_list [self#hwm_gen_push_eip loc];
                	            hwm_stmt_list := List.append !hwm_stmt_list [self#hwm_gen_call_stmt_for_function var.vname (Cil.unrollTypeDeep var.vtype) exp_lst loc];
								hwm_stmt_list := List.append !hwm_stmt_list [self#hwm_gen_stack_pop_params_stmt_for_casm_function exp_lst loc];
								
								ignore(
									match lval with
      									| None -> hwm_stmt_list := !hwm_stmt_list;
      									| Some lv -> hwm_stmt_list := List.append !hwm_stmt_list [(self#hwm_gen_return_result lv loc)];
								);
													
								(* List.iter (Printer.pp_stmt (Format.std_formatter)) !hwm_stmt_list; *)
								
								let newStatement = Cil.mkStmt(Block(Cil.mkBlock(!hwm_stmt_list))) in
									newStatement.labels <- s.labels;
									s.labels <- [];
								newStatement
							
							end
						else
							begin
								s
							end

	                end
	                | _ -> s  (* don't change *)
	            end

				| _ -> 
					begin
						if (hwm_is_casm_function) then 
							begin
								Self.result "\n Ignoring void statement within CASM function.\n";
								s
							end
						else
							begin
								s  (* don't change *)
							end
							
					end
				
 		   	)
		)


	method vglob_aux s =
	    match s with
	    | GFun(f,_) ->
    		begin
		        Self.result "\n function-start (%s) ---" f.svar.vname;	          
				if (Str.string_match (Str.regexp "casm_") f.svar.vname 0) then
					begin
						hwm_is_casm_function <- true;
					end
				else
					begin
						hwm_is_casm_function <- false;
					end
				;					
		        
		        Cil.DoChildrenPost(
		        	fun s -> 
		        	Self.result "\n --- function-end (%s)" f.svar.vname; 
		        	s
		        )
    		end
	    		    	
	    | _ -> Cil.SkipChildren



end;;


(* plugin main function *)    		
let run () =
	Self.result "Embedding HWM...\n";
	Self.result "Before embedding:\n%a" Printer.pp_file (Ast.get ());
	Visitor.visitFramacFile (new embed_hwm_visitor) (Ast.get ()) ;
	Self.result "After embedding:\n%a" Printer.pp_file (Ast.get ());
	Self.result "Done.\n";
	()

(* extend frama-c main interface *)
let () = Db.Main.extend run





