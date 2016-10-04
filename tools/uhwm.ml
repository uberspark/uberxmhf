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




let mkFunTyp (rt : typ) (args : (string * typ) list) : typ =
  TFun(rt, Some(List.map (fun a -> (fst a, snd a, [])) args), false, [])


(*
	**************************************************************************
	global variables
	**************************************************************************
*)
let g_uhwm_collectlabels_for_casm_function = ref false;;
let g_casmfunc_stmts = ((Hashtbl.create 32) : ((string,Cil_types.stmt) Hashtbl.t));;
let g_casmfunc_to_stmthtbl = ((Hashtbl.create 32) : ((string,(string,Cil_types.stmt) Hashtbl.t)  Hashtbl.t));;


  
(* embedding hwm AST visitor *)
class embed_hwm_visitor = object (self)
	inherit Visitor.frama_c_inplace

	val mutable hwm_is_casm_function: bool = false
	val mutable hwm_function_name: string = ""

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


	method private hwm_process_call_stmt_for_c_function s lval exp exp_lst loc = 
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
	            

	method private hwm_casm_function_add_ci_label_stmt_to_hash lbl_name lbl_stmt = 
			Self.result "\nadding label %s for function %s in hash..." lbl_name hwm_function_name;
			Hashtbl.add g_casmfunc_stmts lbl_name lbl_stmt;
			()


	method private hwm_casm_function_gen_stmt_for_ci_label s var exp_lst loc = 
    	let ci_macro_stmt_list = ref [] in
    	let ci_label_exp = (List.nth exp_lst 0) in 
	    let ci_label_string = ref "" in 
	    	ci_macro_stmt_list := List.append !ci_macro_stmt_list [self#hwm_gen_call_stmt_for_function var.vname (Cil.unrollTypeDeep var.vtype) exp_lst loc];
			match ci_label_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_label_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_label operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock(!ci_macro_stmt_list))) in
				result_stmt.labels <- [Label(!ci_label_string, loc, true)];
				self#hwm_casm_function_add_ci_label_stmt_to_hash !ci_label_string result_stmt;
				result_stmt	


	method private hwm_casm_function_gen_stmt_for_ci_jmplabel s var exp_lst loc = 
    	let ci_jmplabel_exp = (List.nth exp_lst 0) in 
	    let ci_jmplabel_string = ref "" in 
			match ci_jmplabel_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_jmplabel_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_jmplabel operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_jmplabel_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let cond_exp= Cil.integer ~loc 1 in 
			let if_stmt_instr = Cil_types.If(cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt


	method private hwm_process_call_stmt_for_casm_function s lval exp exp_lst loc = 
	    match exp.enode with
		    | Lval(Var(var), _) ->
    			begin
						Self.result "\n casm insn macro call: %s" var.vname;
						
						if ((compare "ci_label" var.vname) = 0) && 	(!g_uhwm_collectlabels_for_casm_function = true)
						 then
							begin
								Self.result "\n casm insn macro call: ci_label found";
								self#hwm_casm_function_gen_stmt_for_ci_label s var exp_lst loc
							end
						else if ((compare "ci_jmplabel" var.vname) = 0) && (!g_uhwm_collectlabels_for_casm_function = false) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmplabel found";
								self#hwm_casm_function_gen_stmt_for_ci_jmplabel s var exp_lst loc
							end
						else
							begin
								s
							end
						
				end

            | _ -> s  (* don't change *)


		
			 
	method vstmt_aux s =
		Cil.ChangeDoChildrenPost(
			s,fun s -> (
				match s.skind with
				| Instr (Call(lval, exp, exp_lst, loc)) ->
				begin
					if (hwm_is_casm_function) then
						begin
							self#hwm_process_call_stmt_for_casm_function s lval exp exp_lst loc
						end
					else
						begin
							self#hwm_process_call_stmt_for_c_function s lval exp exp_lst loc
						end
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
				hwm_function_name <- f.svar.vname;
				Hashtbl.clear g_casmfunc_stmts;

		        Self.result "\n function-start (%s) ---" hwm_function_name;	          

				if (Str.string_match (Str.regexp "casm_") hwm_function_name 0) then
					begin
						hwm_is_casm_function <- true;
						Cil.DoChildrenPost(
				        	fun s -> 
				        	Hashtbl.add g_casmfunc_to_stmthtbl hwm_function_name (Hashtbl.copy g_casmfunc_stmts);
							Hashtbl.clear g_casmfunc_stmts;
				        	Self.result "\n --- function-end (%s)" hwm_function_name; 
				        	s
				        )
					end
				else
					begin
						hwm_is_casm_function <- false;
						Cil.DoChildrenPost(
				        	fun s -> 
				        	Self.result "\n --- function-end (%s)" hwm_function_name; 
				        	s
				        )
					end


				
				
		        
    		end
	    		    	
	    | _ -> Cil.SkipChildren



end;;


(* plugin main function *)    		
let run () =
	Self.result "Before embedding:\n%a" Printer.pp_file (Ast.get ());
	Self.result "Embedding HWM (Pass-1)...\n";
	g_uhwm_collectlabels_for_casm_function := true;
	Visitor.visitFramacFile (new embed_hwm_visitor) (Ast.get ()) ;
	
	(* debug *)
	(*Printer.pp_stmt (Format.std_formatter) (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl "casm_funkyfunc") "x"); 
	Printer.pp_stmt (Format.std_formatter) (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl "casm_funkyfunc_2") "y"); 
	*)
	
	Self.result "Embedding HWM (Pass-2)...\n";
	g_uhwm_collectlabels_for_casm_function := false;
	Visitor.visitFramacFile (new embed_hwm_visitor) (Ast.get ()) ;
	Self.result "After embedding:\n%a" Printer.pp_file (Ast.get ());
	Self.result "Done.\n";
	()

(* extend frama-c main interface *)
let () = Db.Main.extend run





