open Theorem_prover.Type
open Theorem_prover.Lexer

open Printf

let main () =
  let token_list = tokenize "%($x:(a).(x))($y:(b).(y))"
  in println_token_list token_list

let () = try main () with
  TokenError err -> 
    printf "Token Error: ";
    match err with
      InvalidToken token -> printf "invalid token '%s'\n" token
