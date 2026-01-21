open Theorem_prover.Type
open Theorem_prover.Lambda
open Theorem_prover.Value
open Theorem_prover.Verify

open Format

let () =
  let x : term = Var "x" in
  let y : term = Var "y" in
  let z : term = Var "z" in
  let w : term = Var "w" in
  let a : term = Var "a" in
  (* rename *)
  let term1 : term  = App (Lam ("x", x, x), Pi ("x", x, x)) in
  let term2 : term  = App (Lam ("y", x, y), Pi ("z", x, z)) in
  let term3 : term  = App (Lam ("x", y, x), Pi ("x", y, x)) in
  let term4 : term  = App (Lam ("x", a, x), Pi ("x", a, x)) in
  assert_alpha_equiv (rename term1 "x" "y") term3;
  assert_alpha_equiv (rename term2 "x" "y") term3;
  assert_alpha_equiv (rename term3 "y" "x") term1;
  assert_alpha_equiv (rename_fresh term1 "x" "a") term4;
  assert_alpha_equiv (rename_fresh term2 "x" "a") term4;
  (* substitution *)
  let term1 : term  = App (Lam ("x", x, App (x, y)), Pi ("y", x, App(x, y))) in
  let term2 : term  = Lam ("x", x, App (y, z)) in
  printf "%a [x := %a] =\n" pp_term term1 pp_term term2;
  printf "  %a\n" pp_term (subst term1 "x" term2);
  printf "  %a\n" pp_term (subst_symb ["a"; "b"] term1 [("x", term2)]);
  printf "  %a\n" pp_term (subst_by_eval term1 [("x", term2)]);
  (* normalization *)
  let defs = [([("B", Type); ("A", Type)], "imply", Some (Pi ("x", Var "A", Var "B")), Type)] in
  let term1 : term = App (Lam ("x", Type, Lam ("y", App (Lam ("z", Type, z), x), App (x, x))), Lam ("w", Type, w)) in
  let term2 : term = App (Lam ("x", Type, Const ("imply", [App (Lam ("y", Type, x), y); x])), Lam ("w", Type, w)) in
  printf "%a ->\n" pp_term term1;
  printf "  %a\n" pp_term (normalize [] term1);
  printf "  %a\n" pp_term (normalize_symb ["a"; "b"] [] term1);
  printf "  %a\n" pp_term (normalize_by_eval [] term1);
  printf "%a ->\n" pp_term term2;
  printf "  %a\n" pp_term (normalize defs term2);
  printf "  %a\n" pp_term (normalize_symb ["a"; "b"] defs term2);
  printf "  %a\n" pp_term (normalize_by_eval defs term2);
