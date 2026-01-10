open Theorem_prover.Verify

let () =
  let defs = read_defs () in
  check_definitions defs
  (* let derivs = read_derivs () in
  let book = verify derivs in
  print_book book *)
