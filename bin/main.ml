open Theorem_prover.Type
open Theorem_prover.Verify

let () =
  let defs = read_defs () in
  List.iter (fun def -> Format.printf "%a\n" pp_def def) defs
  (* let derivs = read_derivs () in
  let book = verify derivs in
  print_book book *)
