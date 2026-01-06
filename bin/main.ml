open Theorem_prover.Type
open Theorem_prover.Verify

let () =
  let book = verify () in
  print_book book
