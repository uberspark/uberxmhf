(*
	frama-c plugin for manifest parsing (main module)
	author: amit vasudevan (amitvasudevan@acm.org)
*)
open umfcommon

let run () =
	Format.printf "proceeding to invoke function within another module...\n";
	umfcommon.subrun();
	Hashtbl.add m_hash "h" "hello";
	Format.printf "back into this module.\n";
	()

let () = Db.Main.extend run

