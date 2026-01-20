open Theorem_prover.Type
open Theorem_prover.Verify

let () =
  if Array.length Sys.argv = 3 then
    let src = open_in Sys.argv.(1) in
    let log = open_out Sys.argv.(2) in
    let def_list = read_defs src in
    let derivs = gen_derivs def_list in
    print_derivs (Format.formatter_of_out_channel log) derivs;
    ignore @@ verify_derivs @@ Vector.to_list derivs;
    close_in src;
    close_out log
  else
    let log = open_in Sys.argv.(1) in
    let derivs = read_derivs log in
    ignore @@ verify_derivs derivs;
    close_in log
