open Theorem_prover.Type
open Theorem_prover.Parser
open Theorem_prover.Lambda
open Theorem_prover.Value

open Format

let () =
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
  printf "%a [x := %a] = %a\n" pp_term term3 pp_term term4 pp_term (subst_symb term3 [("x", term4)]);
  printf "%b\n" (alpha_equiv term1 term2);

  let defs = [([("B", Type); ("A", Type)], "imply", Some (Pi ("x", Var "A", Var "B")), Type)] in
  let (term1, _) = parse "%($x:(*).($y:(%($z:(*).(z))(x)).(%(x)(x))))($w:(*).(w))" in
  let (term2, _) = parse "%($x:(*).(imply[(%($y:(*).(x))(y)),(x)]))($w:(*).(w))" in
  printf "%a ->\n" pp_term term1;
  printf "  %a\n" pp_term (normalize [] term1);
  printf "  %a\n" pp_term (normalize_symb [] term1);
  printf "  %a\n" pp_term (normalize_by_eval [] term1);

  printf "%a ->\n" pp_term term2;
  printf "  %a\n" pp_term (normalize defs term2);
  printf "  %a\n" pp_term (normalize_symb defs term2);
  printf "  %a\n" pp_term (normalize_by_eval defs term2);
