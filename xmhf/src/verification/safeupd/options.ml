(* options.ml
 * module containing helper functions related to command-line parameter
 * parsing
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
*)

module C = Cil
module E = Errormsg

let outFile : string ref = ref ""
let (|>) (a : 'a) (f : 'a -> 'b) : 'b = f a
let fst3 (a,_,_) = a
let sargs (f : 'b -> 'a -> 'c) (x : 'a) (y : 'b) : 'c = f y x

let merge : bool ref = ref false

let options_ref = ref []

let align () =
  let options = !options_ref in
  
  let left = try
      options
      |> List.map fst3
      |> List.map String.length
      |> List.sort (sargs compare)
      |> List.hd
    with Not_found -> 0
  in
  
  let left = left + 4 in
  
  let width = 78 - left in
  
  let rec wrap str =
    if String.length str <= width then str else
    
    let break, skip =
      try let break = String.rindex_from str width ' ' in
        try String.index (String.sub str 0 break) '\n', 1
        with Not_found -> break, 1
      with Not_found -> width, 0
    in
    
    let lstr, rstr =
      String.sub str 0 break,
      String.sub str (break + skip) (String.length str - break - skip)
    in
    lstr ^ "\n" ^ String.make left ' ' ^ wrap rstr
  in
  
  List.map (fun (arg, action, str) ->
    if arg = "" then arg, action, "\n" ^ str ^ "\n"
    else let pre = String.make (left - String.length arg - 3) ' ' in
    arg, action, pre ^ wrap str)
  options

let options = [
  
  "--out", Arg.Set_string outFile, "Set the name of the output file";
  "--help", Arg.Unit (fun () -> Arg.usage (align ()) ""; exit 0), "Show this help message";
  "--merge", Arg.Set merge, "Operate in CIL merger mode";
  "--warnall", Arg.Set E.warnFlag, "Show optional warnings";
  "--envmachine",
   Arg.Unit (fun _ ->
     try
       let machineModel = Sys.getenv "CIL_MACHINE" in
       Cil.envMachine := Some (Machdepenv.modelParse machineModel);
       E.log "CIL_MACHINE=%s\n" machineModel;
     with 
       Not_found ->
	 ignore (E.error "CIL_MACHINE environment variable is not set")
     | Failure msg ->
	 ignore (E.error "CIL_MACHINE machine model is invalid: %s" msg)),
   " Use machine model specified in CIL_MACHINE environment variable";

]

let _ = options_ref := options;;


