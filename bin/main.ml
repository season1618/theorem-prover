open Theorem_prover.Type
open Theorem_prover.Lexer
open Theorem_prover.Parser

open Printf

let main () =
  let token_list = tokenize "%($x:(a).(abc[(a),(*),(@)]))(?y:(b).(def[]))" in
  let (term, _) = parse_term token_list in
  printf "%a\n" pp_term term

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
