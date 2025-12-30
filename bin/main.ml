open Theorem_prover.Type
open Theorem_prover.Lexer
open Theorem_prover.Parser
open Theorem_prover.Verify

open Printf

let parse str = parse_term (tokenize str)

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

  let (term, _) = parse "%($x:(*).($y:(%($z:(*).(z))(x)).(%(x)(not[(x)]))))($w:(*).(w))" in
  printf "%a -> %a\n" pp_term term pp_term (beta_reduction term);

  let book = verify () in
  print_book book

let () =
  try main () with
  | TokenError err ->
      printf "Token Error: ";
      (match err with
      | InvalidToken token -> printf "invalid token '%s'\n" token)
  | SyntaxError err ->
      printf "Syntax Error: ";
      (match err with
      | Empty -> printf "empty expression\n"
      | UnexpectedToken (expected, actual) ->
          printf "'%a' is expected, but '%a' is actual\n" pp_token expected pp_token actual
      | NoToken expected ->
          printf "'%a' is expected, but no token\n" pp_token expected
      | InvalidVariable name ->
          printf "'%s' is invalid as a variable name\n" name
      | NoVariable -> printf "a variable is expected, but not found\n")
  | DerivError err ->
      printf "Derivation Error: ";
      (match err with
      | NotSort term ->
          printf "'%a' must be sort ('*' or '□')\n" pp_term term
      | NotSameName (x1, x2) ->
          printf "two variables '%s' and '%s' must be same\n" x1 x2
      | NotAlphaEquivalence (t1, t2) ->
          printf "two terms '%a' and '%a' must be alpha equivalent\n" pp_term t1 pp_term t2
      | EmptyContext ->
          printf "the context must be non-empty\n"
      | NotSameLengthContext (ctx1, ctx2) ->
          printf "the context length do not match\n";
          printf "'%a'\n" pp_ctx ctx1;
          printf "'%a'\n" pp_ctx ctx2
      | NotSameLengthDefinitions (defs1, defs2) ->
          printf "the definitions length do not match\n";
          printf "'%a'\n" pp_defs defs1;
          printf "'%a'\n" pp_defs defs2
      )
