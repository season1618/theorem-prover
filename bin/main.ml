open Theorem_prover.Type
open Theorem_prover.Verify

let () =
  let def_list = read_defs () in
  let derivs = gen_derivs def_list in
  print_derivs derivs;
  let book = verify_derivs @@ Vector.to_list derivs in
  print_book book
