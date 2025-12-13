open Theorem_prover.Type
open Theorem_prover.Lexer

let () = println_token_list (tokenize "%($x:(a).(x))($y:(b).(y))")
