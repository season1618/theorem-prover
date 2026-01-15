open Theorem_prover.Type
open Theorem_prover.Verify

let () =
  let src = open_in Sys.argv.(1) in
  let log = open_out Sys.argv.(2) in
  let def_list = read_defs src in
  let derivs = gen_derivs def_list in
  print_derivs (Format.formatter_of_out_channel log) derivs;
  let book = verify_derivs @@ Vector.to_list derivs in
  print_book book;
  close_in src;
  close_out log
