open Theorem_prover.Type
open Theorem_prover.Verify

let () =
  let derivs = read_derivs () in
  let book = verify derivs in
  print_book book
