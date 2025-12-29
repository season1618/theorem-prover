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
  printf "%a [x = y] = %a\n" pp_term term1 pp_term (assign term1 "x" "y");
  printf "%a [x = y] = %a\n" pp_term term2 pp_term (assign term2 "x" "y");
  printf "%b\n" (alpha_equiv term1 term2);

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
      )
