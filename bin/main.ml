open Theorem_prover.Type
open Theorem_prover.Parser
open Theorem_prover.Verify

open Format

let main () =
  let (term, _) = parse "%($x:(a).(abc[(a),(*),(@)]))(?y:(b).(def[]))" in
  printf "%a\n" pp_term term;

  let (term1, _) = parse "%($x:(x).(x))(?x:(x).(x))" in
  let (term2, _) = parse "%($y:(x).(y))(?z:(x).(z))" in
  let (term3, _) = parse "%($x:(x).(x))($y:(y).(x))" in
  let (term4, _) = parse "$x:(*).(x)" in
  printf "%a [x := y] = %a\n" pp_term term1 pp_term (rename term1 "x" "y");
  printf "%a [x := y] = %a\n" pp_term term2 pp_term (rename term2 "x" "y");
  printf "%a [x := a] = %a\n" pp_term term1 pp_term (rename_fresh term1 "x" "a");
  printf "%a [x := a] = %a\n" pp_term term2 pp_term (rename_fresh term2 "x" "a");
  printf "%a [x := %a] = %a\n" pp_term term3 pp_term term4 pp_term (subst term3 "x" term4);
  printf "%b\n" (alpha_equiv term1 term2);

  let defs = [([("B", Type); ("A", Type)], "imply", Some (Pi ("x", Var "A", Var "B")), Type)] in
  let (term1, _) = parse "%($x:(*).($y:(%($z:(*).(z))(x)).(%(x)(x))))($w:(*).(w))" in
  let (term2, _) = parse "%($x:(*).(imply[(%($y:(*).(x))(y)),(x)]))($w:(*).(w))" in
  printf "%a -> %a\n" pp_term term1 pp_term (beta_delta_reduction [] term1);
  printf "%a -> %a\n" pp_term term2 pp_term (beta_delta_reduction defs term2);

  let book = verify () in
  print_book book

let () = main ()
