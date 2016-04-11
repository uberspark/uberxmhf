(*
	frama-c plugin for manifest parsing (common library module)
	author: amit vasudevan (amitvasudevan@acm.org)
*)

let m_hash = ((Hashtbl.create 32) : ((string,string)  Hashtbl.t));;
      
let subrun () =
	Format.printf "hello world from sub module\n";
	Format.printf "returning back to main module\n";
	()


