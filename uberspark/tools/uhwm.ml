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
let g_casmfunc_stmts = ((Hashtbl.create 32) : ((string,Cil_types.stmt) Hashtbl.t));;
let g_casmfunc_to_stmthtbl = ((Hashtbl.create 32) : ((string,(string,Cil_types.stmt) Hashtbl.t)  Hashtbl.t));;
(* let g_func_decls = ((Hashtbl.create 32) : ((string,((string * Cil_types.typ * Cil_types.attributes) list))  Hashtbl.t));; *)
let g_func_decls = ((Hashtbl.create 32) : ((string,Cil_types.varinfo)  Hashtbl.t));;
let g_uhwm_pass = ref 0;;






(*
	**************************************************************************
	global constants
	**************************************************************************
*)
let uhwm_pass_1 = 1;;
let uhwm_pass_2 = 2;;
let eflags_cf = 1;;
let eflags_zf = 0x00000040;;



  
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


	method private hwm_casm_function_gen_stmt_for_ci_jc s var exp_lst loc = 
    	let ci_jc_exp = (List.nth exp_lst 0) in 
	    let ci_jc_string = ref "" in 
			match ci_jc_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_jc_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_jc operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_jc_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let var_eflags = Cil.makeVarinfo true false "xmhfhwm_cpu_eflags" Cil.uintType in
			let cond_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_cf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let if_stmt_instr = Cil_types.If(cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt



	method private hwm_casm_function_gen_stmt_for_ci_jnc s var exp_lst loc = 
    	let ci_jnc_exp = (List.nth exp_lst 0) in 
	    let ci_jnc_string = ref "" in 
			match ci_jnc_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_jnc_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_jnc operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_jnc_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let var_eflags = Cil.makeVarinfo true false "xmhfhwm_cpu_eflags" Cil.uintType in
			let cond_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_cf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let neg_cond_exp = Cil.new_exp ~loc (UnOp(LNot, cond_exp, Cil.intType)) in
			let if_stmt_instr = Cil_types.If(neg_cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt


	method private hwm_casm_function_gen_stmt_for_ci_jz s var exp_lst loc = 
    	let ci_jz_exp = (List.nth exp_lst 0) in 
	    let ci_jz_string = ref "" in 
			match ci_jz_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_jz_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_jz operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_jz_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let var_eflags = Cil.makeVarinfo true false "xmhfhwm_cpu_eflags" Cil.uintType in
			let cond_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_zf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let if_stmt_instr = Cil_types.If(cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt


	(* ci_jnz CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jnz s var exp_lst loc = 
    	let ci_jnz_exp = (List.nth exp_lst 0) in 
	    let ci_jnz_string = ref "" in 
			match ci_jnz_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_jnz_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_jnz operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_jnz_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let var_eflags = Cil.makeVarinfo true false "xmhfhwm_cpu_eflags" Cil.uintType in
			let cond_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_zf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let neg_cond_exp = Cil.new_exp ~loc (UnOp(LNot, cond_exp, Cil.intType)) in
			let if_stmt_instr = Cil_types.If(neg_cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt


	(* ci_jbe CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jbe s var exp_lst loc = 
    	let ci_jbe_exp = (List.nth exp_lst 0) in 
	    let ci_jbe_string = ref "" in 
			match ci_jbe_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_jbe_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_jbe operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_jbe_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let var_eflags = Cil.makeVarinfo true false "xmhfhwm_cpu_eflags" Cil.uintType in
			let zf_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_zf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let cf_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_cf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let cond_exp = Cil.new_exp ~loc (BinOp(BAnd, zf_exp, cf_exp, Cil.intType)) in
			let if_stmt_instr = Cil_types.If(cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt



	(* ci_ja CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_ja s var exp_lst loc = 
    	let ci_ja_exp = (List.nth exp_lst 0) in 
	    let ci_ja_string = ref "" in 
			match ci_ja_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_ja_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_ja operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let goto_stmt = (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl hwm_function_name) !ci_ja_string) in  
			let instr = Cil_types.Goto(ref goto_stmt, loc) in
			let new_stmt = Cil.mkStmt (instr) in
			let var_eflags = Cil.makeVarinfo true false "xmhfhwm_cpu_eflags" Cil.uintType in
			let zf_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_zf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let cf_exp = Cil.new_exp ~loc (BinOp(BAnd, (Cil.evar ~loc:loc var_eflags), (Cil.integer ~loc eflags_cf), (Cil.unrollTypeDeep var_eflags.vtype))) in
			let neg_zf_exp = Cil.new_exp ~loc (UnOp(LNot, zf_exp, Cil.intType)) in
			let neg_cf_exp = Cil.new_exp ~loc (UnOp(LNot, cf_exp, Cil.intType)) in
			let cond_exp = Cil.new_exp ~loc (BinOp(BAnd, neg_zf_exp, neg_cf_exp, Cil.intType)) in
			let if_stmt_instr = Cil_types.If(cond_exp, Cil.mkBlock([new_stmt]), Cil.mkBlock([]), loc) in
			let if_stmt_stmt = Cil.mkStmt(if_stmt_instr) in
			let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([if_stmt_stmt]))) in 
				result_stmt



	(* ci_call CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_call s var exp_lst loc = 
    	let ci_call_exp = (List.nth exp_lst 0) in 
	    let ci_call_string = ref "" in 
			match ci_call_exp.enode with
		    	| Const(CStr(param_string)) -> 
		    		(
		    			ci_call_string := param_string;
		    		);
		    	| _ -> 
		    		(
		    			Self.result "\n Illegal ci_call operand -- not a string constant. Abort!\n";
		    			ignore(exit 1);
		    		);
		    ;	
			let f_varinfo = Hashtbl.find g_func_decls !ci_call_string in 
			let ci_call_exp_lst = ref [] in
			
				Self.result "ci_call processing: function name: %s\n" f_varinfo.vname;
				
				match f_varinfo.vtype with
		    		| TFun(rettype, args, isva, a) -> 
		    			(
							let argslist = (Cil.argsToList args) in
								Self.result "\n    params=%u" (List.length argslist);	          
								for index = 0 to ((List.length argslist)-1) do
									begin
									let tuple = (List.nth argslist index) in
									let (n,t,_) = tuple in
										Self.result "    param-%u: name=%s\n" (index+1) n;
										(* Printer.pp_typ (Format.std_formatter) t; *)
										let var_esp = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_esp" Cil.uintType in
										let esp_ptr_exp = Cil.new_exp ~loc (CastE(TPtr(Cil.uintType,[]), (Cil.evar ~loc:loc var_esp))) in
										let esp_off_exp = Cil.new_exp ~loc (BinOp(Mult, (Cil.integer ~loc 4), (Cil.integer ~loc (index+1)), Cil.uintType)) in 
										let esp_addr_exp = Cil.new_exp ~loc (BinOp(PlusPI, esp_ptr_exp, esp_off_exp, TPtr(Cil.uintType,[]))) in 
										let esp_mem_exp = Cil.new_exp ~loc (Lval(Cil.mkMem ~addr:esp_addr_exp ~off:NoOffset)) in 
										let param_exp = Cil.new_exp ~loc (CastE(t, esp_mem_exp)) in 
											ci_call_exp_lst := List.append !ci_call_exp_lst [param_exp];
									end
								done
								; 
			    		);
					    
					|_ -> ();
				;
				let instr = Cil_types.Call(None, Cil.evar ~loc:loc f_varinfo, !ci_call_exp_lst, loc) in
				let result_stmt = Cil.mkStmtOneInstr (instr) in
				(* let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([]))) in *) 
					result_stmt



	(* ci_ret and ci_ret32 CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_ret s var exp_lst loc = 
		let var_esp = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_esp" Cil.uintType in
		let var_eip = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eip" Cil.uintType in
		let exp_var_esp = (Cil.evar ~loc:loc var_esp) in 
		let exp_var_eip = (Cil.evar ~loc:loc var_eip) in 
		let exp_eip_valueaddr = Cil.new_exp ~loc (CastE(TPtr(Cil.uintType,[]), exp_var_esp)) in
		let exp_eip_valuemem = Cil.new_exp ~loc (Lval(Cil.mkMem ~addr:exp_eip_valueaddr ~off:NoOffset)) in
		let var_eip_lval = (Cil.var var_eip) in
		let eip_assign_instr = Cil_types.Set(var_eip_lval, exp_eip_valuemem, loc) in
		let eip_assign_stmt = Cil.mkStmtOneInstr (eip_assign_instr) in
		let var_esp_increxp = Cil.new_exp ~loc (BinOp(PlusPI, exp_var_esp, (Cil.integer ~loc 4), Cil.uintType)) in		
		let var_esp_lval = (Cil.var var_esp) in
		let var_esp_incrstmt_instr = Cil_types.Set(var_esp_lval, var_esp_increxp, loc) in
		let var_esp_incrstmt = Cil.mkStmtOneInstr (var_esp_incrstmt_instr) in
		let ret_stmt = Cil.mkStmt(Cil_types.Return(None, loc)) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([eip_assign_stmt; var_esp_incrstmt; ret_stmt]))) in
			result_stmt



	(* ci_ret64 CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_ret64 s var exp_lst loc = 
		let var_esp = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_esp" Cil.uintType in
		let var_eip = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eip" Cil.uintType in
		let exp_var_esp = (Cil.evar ~loc:loc var_esp) in 
		let exp_var_eip = (Cil.evar ~loc:loc var_eip) in 
		let exp_eip_valueaddr = Cil.new_exp ~loc (CastE(TPtr(Cil.uintType,[]), exp_var_esp)) in
		let exp_eip_valuemem = Cil.new_exp ~loc (Lval(Cil.mkMem ~addr:exp_eip_valueaddr ~off:NoOffset)) in
		let var_eip_lval = (Cil.var var_eip) in
		let eip_assign_instr = Cil_types.Set(var_eip_lval, exp_eip_valuemem, loc) in
		let eip_assign_stmt = Cil.mkStmtOneInstr (eip_assign_instr) in
		let var_esp_increxp = Cil.new_exp ~loc (BinOp(PlusPI, exp_var_esp, (Cil.integer ~loc 4), Cil.uintType)) in		
		let var_esp_lval = (Cil.var var_esp) in
		let var_esp_incrstmt_instr = Cil_types.Set(var_esp_lval, var_esp_increxp, loc) in
		let var_esp_incrstmt = Cil.mkStmtOneInstr (var_esp_incrstmt_instr) in
		let var_edx = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_edx" Cil.uintType in
		let var_eax = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eax" Cil.uintType in
		let exp1 = Cil.new_exp ~loc (BinOp(Shiftlt, (Cil.evar ~loc:loc var_edx), (Cil.integer ~loc 32), (TInt(IULongLong,[])))) in
		let exp2 = Cil.new_exp ~loc (CastE(TInt(IULongLong,[]), exp1)) in
		let exp3 = Cil.new_exp ~loc (BinOp(BOr, exp2 ,(Cil.evar ~loc:loc var_eax), (TInt(IULongLong,[])))) in
		let ret_stmt = Cil.mkStmt(Cil_types.Return((Some exp3), loc)) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([eip_assign_stmt; var_esp_incrstmt; ret_stmt]))) in
			result_stmt



	(* ci_lret CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_lret s var exp_lst loc = 
		let var_esp = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_esp" Cil.uintType in
		let var_eip = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eip" Cil.uintType in
		let var_cs_sel = Cil.makeVarinfo true false "xmhfhwm_cpu_cs_selector" Cil.uintType in
		let exp_var_esp = (Cil.evar ~loc:loc var_esp) in 
		let exp_var_eip = (Cil.evar ~loc:loc var_eip) in 
		let exp_eip_valueaddr = Cil.new_exp ~loc (CastE(TPtr(Cil.uintType,[]), exp_var_esp)) in
		let exp_eip_valuemem = Cil.new_exp ~loc (Lval(Cil.mkMem ~addr:exp_eip_valueaddr ~off:NoOffset)) in
		let var_eip_lval = (Cil.var var_eip) in
		let var_cs_sel_lval = (Cil.var var_cs_sel) in
		let eip_assign_instr = Cil_types.Set(var_eip_lval, exp_eip_valuemem, loc) in
		let eip_assign_stmt = Cil.mkStmtOneInstr (eip_assign_instr) in
		let cs_sel_assign_instr = Cil_types.Set(var_cs_sel_lval, exp_eip_valuemem, loc) in
		let cs_sel_assign_stmt = Cil.mkStmtOneInstr (cs_sel_assign_instr) in
		let var_esp_increxp = Cil.new_exp ~loc (BinOp(PlusPI, exp_var_esp, (Cil.integer ~loc 4), Cil.uintType)) in		
		let var_esp_lval = (Cil.var var_esp) in
		let var_esp_incrstmt_instr = Cil_types.Set(var_esp_lval, var_esp_increxp, loc) in
		let var_esp_incrstmt = Cil.mkStmtOneInstr (var_esp_incrstmt_instr) in
		let ret_stmt = Cil.mkStmt(Cil_types.Return(None, loc)) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([eip_assign_stmt; var_esp_incrstmt; cs_sel_assign_stmt; var_esp_incrstmt; ret_stmt]))) in
			result_stmt



	(* ci_jmpapentry CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jmpapentry s var exp_lst loc = 
		let void_ftyp = mkFunTyp Cil.voidType [] in
		let vdrv_apentry_fvname = "xmhfhwm_vdriver_apentry" in
		let vdrv_apentry_fvar = Cil.findOrCreateFunc (Ast.get ()) vdrv_apentry_fvname void_ftyp in
		let vdrv_apentry_instr = Cil_types.Call(None, Cil.evar ~loc:loc vdrv_apentry_fvar, [], loc) in
		let vdrv_apentry_stmt = Cil.mkStmtOneInstr (vdrv_apentry_instr) in
		let hlt_fvname = "_impl_xmhfhwm_cpu_insn_hlt" in
		let hlt_fvar = Cil.findOrCreateFunc (Ast.get ()) hlt_fvname void_ftyp in
		let hlt_instr = Cil_types.Call(None, Cil.evar ~loc:loc hlt_fvar, [], loc) in
		let hlt_stmt = Cil.mkStmtOneInstr (hlt_instr) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([vdrv_apentry_stmt; hlt_stmt]))) in
			result_stmt




	(* ci_jmpsmpcommon CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jmpsmpcommon s var exp_lst loc = 
		let void_ftyp = mkFunTyp Cil.voidType [] in
		let vdrv_smpcommon_fvname = "xmhfhwm_vdriver_smpcommon" in
		let vdrv_smpcommon_fvar = Cil.findOrCreateFunc (Ast.get ()) vdrv_smpcommon_fvname void_ftyp in
		let vdrv_smpcommon_instr = Cil_types.Call(None, Cil.evar ~loc:loc vdrv_smpcommon_fvar, [], loc) in
		let vdrv_smpcommon_stmt = Cil.mkStmtOneInstr (vdrv_smpcommon_instr) in
		let hlt_fvname = "_impl_xmhfhwm_cpu_insn_hlt" in
		let hlt_fvar = Cil.findOrCreateFunc (Ast.get ()) hlt_fvname void_ftyp in
		let hlt_instr = Cil_types.Call(None, Cil.evar ~loc:loc hlt_fvar, [], loc) in
		let hlt_stmt = Cil.mkStmtOneInstr (hlt_instr) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([vdrv_smpcommon_stmt; hlt_stmt]))) in
			result_stmt



	(* ci_jmpsentinel CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jmpsentinel s var exp_lst loc = 
		let void_ftyp = mkFunTyp Cil.voidType [] in
		let vdrv_sentinel_fvname = "xmhfhwm_vdriver_sentinel" in
		let vdrv_sentinel_fvar = Cil.findOrCreateFunc (Ast.get ()) vdrv_sentinel_fvname void_ftyp in
		let vdrv_sentinel_instr = Cil_types.Call(None, Cil.evar ~loc:loc vdrv_sentinel_fvar, [], loc) in
		let vdrv_sentinel_stmt = Cil.mkStmtOneInstr (vdrv_sentinel_instr) in
		let hlt_fvname = "_impl_xmhfhwm_cpu_insn_hlt" in
		let hlt_fvar = Cil.findOrCreateFunc (Ast.get ()) hlt_fvname void_ftyp in
		let hlt_instr = Cil_types.Call(None, Cil.evar ~loc:loc hlt_fvar, [], loc) in
		let hlt_stmt = Cil.mkStmtOneInstr (hlt_instr) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([vdrv_sentinel_stmt; hlt_stmt]))) in
			result_stmt



	(* ci_jmpuobjep CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jmpuobjep s var exp_lst loc = 
		let void_ftyp = mkFunTyp Cil.voidType [] in
		let vdrv_uobjep_fvname = "xmhfhwm_vdriver_uobjep" in
		let vdrv_uobjep_fvar = Cil.findOrCreateFunc (Ast.get ()) vdrv_uobjep_fvname void_ftyp in
		let vdrv_uobjep_instr = Cil_types.Call(None, Cil.evar ~loc:loc vdrv_uobjep_fvar, [], loc) in
		let vdrv_uobjep_stmt = Cil.mkStmtOneInstr (vdrv_uobjep_instr) in
		let hlt_fvname = "_impl_xmhfhwm_cpu_insn_hlt" in
		let hlt_fvar = Cil.findOrCreateFunc (Ast.get ()) hlt_fvname void_ftyp in
		let hlt_instr = Cil_types.Call(None, Cil.evar ~loc:loc hlt_fvar, [], loc) in
		let hlt_stmt = Cil.mkStmtOneInstr (hlt_instr) in
		let var_eax = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eax" Cil.uintType in
		let var_eip = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eip" Cil.uintType in
		let var_eip_lval = (Cil.var var_eip) in
		let eip_assign_instr = Cil_types.Set(var_eip_lval, (Cil.evar ~loc:loc var_eax), loc) in
		let eip_assign_stmt = Cil.mkStmtOneInstr (eip_assign_instr) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([eip_assign_stmt; vdrv_uobjep_stmt; hlt_stmt]))) in
			result_stmt



	(* ci_jmpvuobretaddr CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jmpvuobjretaddr s var exp_lst loc = 
		let void_ftyp = mkFunTyp Cil.voidType [] in
		let vdrv_vuobjretaddr_fvname = "xmhfhwm_vdriver_vuobjretaddr" in
		let vdrv_vuobjretaddr_fvar = Cil.findOrCreateFunc (Ast.get ()) vdrv_vuobjretaddr_fvname void_ftyp in
		let vdrv_vuobjretaddr_instr = Cil_types.Call(None, Cil.evar ~loc:loc vdrv_vuobjretaddr_fvar, [], loc) in
		let vdrv_vuobjretaddr_stmt = Cil.mkStmtOneInstr (vdrv_vuobjretaddr_instr) in
		let hlt_fvname = "_impl_xmhfhwm_cpu_insn_hlt" in
		let hlt_fvar = Cil.findOrCreateFunc (Ast.get ()) hlt_fvname void_ftyp in
		let hlt_instr = Cil_types.Call(None, Cil.evar ~loc:loc hlt_fvar, [], loc) in
		let hlt_stmt = Cil.mkStmtOneInstr (hlt_instr) in
		let var_esp = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_esp" Cil.uintType in
		let var_eip = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eip" Cil.uintType in
		let exp_var_esp = (Cil.evar ~loc:loc var_esp) in 
		let exp_var_eip = (Cil.evar ~loc:loc var_eip) in 
		let exp_eip_valueaddr = Cil.new_exp ~loc (CastE(TPtr(Cil.uintType,[]), exp_var_esp)) in
		let exp_eip_valuemem = Cil.new_exp ~loc (Lval(Cil.mkMem ~addr:exp_eip_valueaddr ~off:NoOffset)) in
		let var_eip_lval = (Cil.var var_eip) in
		let eip_assign_instr = Cil_types.Set(var_eip_lval, exp_eip_valuemem, loc) in
		let eip_assign_stmt = Cil.mkStmtOneInstr (eip_assign_instr) in
		let var_esp_increxp = Cil.new_exp ~loc (BinOp(PlusPI, exp_var_esp, (Cil.integer ~loc 4), Cil.uintType)) in		
		let var_esp_lval = (Cil.var var_esp) in
		let var_esp_incrstmt_instr = Cil_types.Set(var_esp_lval, var_esp_increxp, loc) in
		let var_esp_incrstmt = Cil.mkStmtOneInstr (var_esp_incrstmt_instr) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([eip_assign_stmt; var_esp_incrstmt; vdrv_vuobjretaddr_stmt; hlt_stmt]))) in
			result_stmt



	(* ci_jmpuuobjretaddr CASM instruction *)
	method private hwm_casm_function_gen_stmt_for_ci_jmpuuobjretaddr s var exp_lst loc = 
		let void_ftyp = mkFunTyp Cil.voidType [] in
		let vdrv_uuobjretaddr_fvname = "xmhfhwm_vdriver_uuobjretaddr" in
		let vdrv_uuobjretaddr_fvar = Cil.findOrCreateFunc (Ast.get ()) vdrv_uuobjretaddr_fvname void_ftyp in
		let vdrv_uuobjretaddr_instr = Cil_types.Call(None, Cil.evar ~loc:loc vdrv_uuobjretaddr_fvar, [], loc) in
		let vdrv_uuobjretaddr_stmt = Cil.mkStmtOneInstr (vdrv_uuobjretaddr_instr) in
		let hlt_fvname = "_impl_xmhfhwm_cpu_insn_hlt" in
		let hlt_fvar = Cil.findOrCreateFunc (Ast.get ()) hlt_fvname void_ftyp in
		let hlt_instr = Cil_types.Call(None, Cil.evar ~loc:loc hlt_fvar, [], loc) in
		let hlt_stmt = Cil.mkStmtOneInstr (hlt_instr) in
		let var_esp = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_esp" Cil.uintType in
		let var_eip = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_eip" Cil.uintType in
		let var_ecx = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_ecx" Cil.uintType in
		let var_edx = Cil.makeVarinfo true false "xmhfhwm_cpu_gprs_edx" Cil.uintType in
		let exp_var_esp = (Cil.evar ~loc:loc var_esp) in 
		let exp_var_eip = (Cil.evar ~loc:loc var_eip) in 
		let exp_var_ecx = (Cil.evar ~loc:loc var_ecx) in 
		let exp_var_edx = (Cil.evar ~loc:loc var_edx) in 
		let var_eip_lval = (Cil.var var_eip) in
		let var_esp_lval = (Cil.var var_esp) in
		let eip_assign_instr = Cil_types.Set(var_eip_lval, exp_var_edx, loc) in
		let eip_assign_stmt = Cil.mkStmtOneInstr (eip_assign_instr) in
		let esp_assign_instr = Cil_types.Set(var_esp_lval, exp_var_ecx, loc) in
		let esp_assign_stmt = Cil.mkStmtOneInstr (esp_assign_instr) in
		let result_stmt = Cil.mkStmt(Block(Cil.mkBlock([eip_assign_stmt; esp_assign_stmt; vdrv_uuobjretaddr_stmt; hlt_stmt]))) in
			result_stmt


	method private hwm_process_call_stmt_for_casm_function s lval exp exp_lst loc = 
	    match exp.enode with
		    | Lval(Var(var), _) ->
    			begin
						Self.result "\n casm insn macro call: %s" var.vname;
						
						if ((compare "ci_label" var.vname) = 0) && 	(!g_uhwm_pass = uhwm_pass_1)
						 then
							begin
								Self.result "\n casm insn macro call: ci_label found";
								self#hwm_casm_function_gen_stmt_for_ci_label s var exp_lst loc
							end
						else if ((compare "ci_jmplabel" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmplabel found";
								self#hwm_casm_function_gen_stmt_for_ci_jmplabel s var exp_lst loc
							end
						else if ((compare "ci_jc" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jc found";
								self#hwm_casm_function_gen_stmt_for_ci_jc s var exp_lst loc
							end
						else if ((compare "ci_jnc" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jnc found";
								self#hwm_casm_function_gen_stmt_for_ci_jnc s var exp_lst loc
							end
						else if ( (compare "ci_jz" var.vname) = 0 || (compare "ci_je" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jz found";
								self#hwm_casm_function_gen_stmt_for_ci_jz s var exp_lst loc
							end
						else if ((compare "ci_jnz" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jnz found";
								self#hwm_casm_function_gen_stmt_for_ci_jnz s var exp_lst loc
							end
						else if ((compare "ci_jbe" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jbe found";
								self#hwm_casm_function_gen_stmt_for_ci_jbe s var exp_lst loc
							end
						else if ((compare "ci_ja" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_ja found";
								self#hwm_casm_function_gen_stmt_for_ci_ja s var exp_lst loc
							end
						else if ((compare "ci_call" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_call found";
								self#hwm_casm_function_gen_stmt_for_ci_call s var exp_lst loc
							end
						else if ((compare "ci_ret" var.vname) = 0 || (compare "ci_ret32" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_ret found";
								self#hwm_casm_function_gen_stmt_for_ci_ret s var exp_lst loc
							end
						else if ((compare "ci_ret64" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_ret64 found";
								self#hwm_casm_function_gen_stmt_for_ci_ret64 s var exp_lst loc
							end
						else if ((compare "ci_lret" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_lret found";
								self#hwm_casm_function_gen_stmt_for_ci_lret s var exp_lst loc
							end
						else if ((compare "ci_jmpapentry" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmpapentry found";
								self#hwm_casm_function_gen_stmt_for_ci_jmpapentry s var exp_lst loc
							end
						else if ((compare "ci_jmpsmpcommon" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmpsmpcommon found";
								self#hwm_casm_function_gen_stmt_for_ci_jmpsmpcommon s var exp_lst loc
							end
						else if ((compare "ci_jmpsentinel" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmpsentinel found";
								self#hwm_casm_function_gen_stmt_for_ci_jmpsentinel s var exp_lst loc
							end
						else if ((compare "ci_jmpuobjep" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmpuobjep found";
								self#hwm_casm_function_gen_stmt_for_ci_jmpuobjep s var exp_lst loc
							end
						else if ((compare "ci_jmpvuobjretaddr" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmpvuobjretaddr found";
								self#hwm_casm_function_gen_stmt_for_ci_jmpvuobjretaddr s var exp_lst loc
							end
						else if ((compare "ci_jmpuuobjretaddr" var.vname) = 0) && (!g_uhwm_pass = uhwm_pass_2) 
						 then
							begin
								Self.result "\n casm insn macro call: ci_jmpuuobjretaddr found";
								self#hwm_casm_function_gen_stmt_for_ci_jmpuuobjretaddr s var exp_lst loc
							end
						else
							begin
								s
							end
						
				end

            | _ -> s  (* don't change *)




	method private hwm_process_call_stmt_for_c_function s lval exp exp_lst loc = 
	    match exp.enode with
		    | Lval(Var(var), _) ->
    			begin
					let hwm_stmt_list = ref [] in
									
					if (Str.string_match (Str.regexp "casm_") var.vname 0) then
						begin
							hwm_stmt_list := self#hwm_gen_stack_push_param_stmts_for_casm_function exp_lst loc;
            	            hwm_stmt_list := List.append !hwm_stmt_list [self#hwm_gen_push_eip loc];
            	            (*hwm_stmt_list := List.append !hwm_stmt_list [self#hwm_gen_call_stmt_for_function var.vname (Cil.unrollTypeDeep var.vtype) exp_lst loc];*)
            	            hwm_stmt_list := List.append !hwm_stmt_list [s];
							hwm_stmt_list := List.append !hwm_stmt_list [self#hwm_gen_stack_pop_params_stmt_for_casm_function exp_lst loc];
							
							(*ignore(
								match lval with
  									| None -> hwm_stmt_list := !hwm_stmt_list;
  									| Some lv -> hwm_stmt_list := List.append !hwm_stmt_list [(self#hwm_gen_return_result lv loc)];
							);*)
												
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
							if (!g_uhwm_pass = uhwm_pass_2) then
								begin
									self#hwm_process_call_stmt_for_c_function s lval exp exp_lst loc
								end
							else
								begin
									s
								end
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


	(* top-level AST node processing *)
	method vglob_aux s =
	    match s with
	    | GFun(f,_) ->
    		begin
				hwm_function_name <- f.svar.vname;
				Hashtbl.clear g_casmfunc_stmts;

		        Self.result "\n function-start (%s) ---" hwm_function_name;	          

				if (!g_uhwm_pass = uhwm_pass_1) then 
					begin
						match f.svar.vtype with
					    	| TFun(rettype, args, isva, a) -> 
					    		(
									let argslist = (Cil.argsToList args) in
										Self.result "\n function type consistent, params=%u" (List.length argslist);	          
										Hashtbl.add g_func_decls f.svar.vname f.svar;
										(*for index = 0 to ((List.length argslist)-1) do
											begin
											let tuple = (List.nth argslist index) in
											let (n,t,_) = tuple in
												Self.result "param: %s\n" n;
												Printer.pp_typ (Format.std_formatter) t;
											end
										done
										;*) 
					    		);
					    	| _ -> 
					    		(
									Self.result "\n function type inconsistent";			    			
									ignore(exit 1);
					    		);
					    ;	
					end
				;
				
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
	    
	    
	    (* | GVarDecl(funspec,var,loc) -> *)
	 	| GVarDecl(var,loc) ->
	    	begin
				Self.result "var decl, name=%s\n" var.vname;
				match var.vtype with
			    	| TFun(rettype, args, isva, a) -> 
			    		(
							if (!g_uhwm_pass = uhwm_pass_1) then
								begin
									let argslist = (Cil.argsToList args) in
										Self.result "\nvar decl: function type, params=%u" (List.length argslist);	          
										Hashtbl.add g_func_decls var.vname var;
										(*for index = 0 to ((List.length argslist)-1) do
											begin
											let tuple = (List.nth argslist index) in
											let (n,t,_) = tuple in
												Self.result "param: %s\n" n;
												Printer.pp_typ (Format.std_formatter) t;
											end
										done
										;*) 
								end
							;
							
			    			Cil.DoChildrenPost(fun s ->	s)
			    		)
			    	| _ ->	Cil.DoChildrenPost(fun s ->	s)
			    	

	    	end
	    		    	
	    | _ -> Cil.SkipChildren



end;;


(* plugin main function *)    		
let run () =
	Self.result "Before embedding:\n%a" Printer.pp_file (Ast.get ());
	
	Self.result "Embedding HWM (Pass-1)...\n";
	g_uhwm_pass := uhwm_pass_1;
	Visitor.visitFramacFile (new embed_hwm_visitor) (Ast.get ()) ;
	
	(* debug *)
	(*Printer.pp_stmt (Format.std_formatter) (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl "casm_funkyfunc") "x"); 
	Printer.pp_stmt (Format.std_formatter) (Hashtbl.find (Hashtbl.find g_casmfunc_to_stmthtbl "casm_funkyfunc_2") "y"); 
	*)
	
	Self.result "Embedding HWM (Pass-2)...\n";
	g_uhwm_pass := uhwm_pass_2;
	Visitor.visitFramacFile (new embed_hwm_visitor) (Ast.get ()) ;

	Self.result "After embedding:\n%a" Printer.pp_file (Ast.get ());
	Self.result "Done.\n";
	()

(* extend frama-c main interface *)
let () = Db.Main.extend run





