(* cammwrite.ml
 * cil analysis module to log memory writes
 * based on logmwrite module that comes with the cil distribution
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 *)
 
open Cil 
open Pretty
module E = Errormsg
module H = Hashtbl
module L = List

(* macro to make a function with specified return type and args *)
let mkFunTyp (rt : typ) (args : (string * typ) list) : typ =
  TFun(rt, Some(L.map (fun a -> (fst a, snd a, [])) args), false, [])


(* Returns true if the given lvalue offset ends in a bitfield access. *) 
let rec is_bitfield lo = match lo with
  | NoOffset -> false
  | Field(fi,NoOffset) -> not (fi.fbitfield = None)
  | Field(_,lo) -> is_bitfield lo
  | Index(_,lo) -> is_bitfield lo 

(* Return an expression that evaluates to the address of the given lvalue.
 * For most lvalues, this is merely AddrOf(lv). However, for bitfields
 * we do some offset gymnastics. 
 *)
let addr_of_lv (lh,lo) = 
  if is_bitfield lo then begin
    (* we figure out what the address would be without the final bitfield
     * access, and then we add in the offset of the bitfield from the
     * beginning of its enclosing comp *) 
    let rec split_offset_and_bitfield lo = match lo with 
      | NoOffset -> failwith "logwrites: impossible" 
      | Field(fi,NoOffset) -> (NoOffset,fi)
      | Field(e,lo) ->  let a,b = split_offset_and_bitfield lo in 
                        ((Field(e,a)),b)
      | Index(e,lo) ->  let a,b = split_offset_and_bitfield lo in
                        ((Index(e,a)),b)
    in 
    let new_lv_offset, bf = split_offset_and_bitfield lo in
    let new_lv = (lh, new_lv_offset) in 
    let enclosing_type = TComp(bf.fcomp, []) in 
    let bits_offset, bits_width = 
      bitsOffset enclosing_type (Field(bf,NoOffset)) in
    let bytes_offset = bits_offset / 8 in 
    let lvPtr = mkCast ~e:(mkAddrOf (new_lv)) ~newt:(charPtrType) in
    (BinOp(PlusPI, lvPtr, (integer bytes_offset), ulongType))
  end else (AddrOf (lh,lo)) 

class logWriteVisitor = object
  inherit nopCilVisitor
  (* Create a prototype for the logging function, but don't put it in the 
   * file *)
  val printfFun =   
    let fdec = emptyFunction "writetomem" in
    fdec.svar.vtype <- TFun(intType, 
                            Some [ ("prio", intType, []);
                                   ("format", charConstPtrType, []) ], 
                            true, []);
    fdec
   
  (* create a prototype for the assert function *)
  val assertFun =
	let assertfdec = emptyFunction "assert" in
	assertfdec.svar.vtype <- mkFunTyp voidType ["exp", charPtrType];
	assertfdec
    

  method vinst (i: instr) : instr list visitAction = 
    match i with 
      Set(lv, e, l) -> begin
        (* Check if we need to log *)
        match lv with 
          (Var(v), off) when not v.vglob -> SkipChildren
        | _ -> let str = Pretty.sprint 80 
                (Pretty.dprintf "Value %%p written to memory at 0x%%08x within file %%s:%%d (%a)\n" d_lval lv)
              in 
              (* ChangeTo 
               * [ Call((None), (Lval(Var(printfFun.svar),NoOffset)), 
               *      [ one ; 
               *        mkString str ; e ; addr_of_lv lv; 
               *        mkString l.file; 
               *        integer l.line], locUnknown);
               * i]
               *)
               ChangeTo 
                [ Call((None), (Lval(Var(assertFun.svar),NoOffset)), 
                     [ addr_of_lv lv ], locUnknown); 
                   
                i]
               
      end 
    | Call(Some lv, f, args, l) -> begin
        (* Check if we need to log *)
        match lv with 
          (Var(v), off) when not v.vglob -> SkipChildren
        | _ -> let str = Pretty.sprint 80 
                (Pretty.dprintf "A return value written to memory at 0x%%08x within file %%s:%%d (%a)\n" d_lval lv)
              in 
              (* ChangeTo 
               * [ Call((None), (Lval(Var(printfFun.svar),NoOffset)), 
               *      [ one ; 
               *        mkString str ; AddrOf lv; 
               *        mkString l.file; 
               *        integer l.line], locUnknown);
               * i]
               *)
               ChangeTo 
                [ Call((None), (Lval(Var(assertFun.svar),NoOffset)), 
                     [ AddrOf lv ], locUnknown);
                i]
               
      end 
    | _ -> SkipChildren

end

let logmwrites (f : file) : unit =
  let vis = new logWriteVisitor in
  visitCilFile vis f

let runanalysis (f : file) : unit =
	E.log "cammwrite: runanalysis...\n";
	logmwrites f
