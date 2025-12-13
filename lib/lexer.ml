open String
open List

open Type

let symbols = ['('; ')'; '['; ']'; ','; '.'; ':'; '*'; '@'; '%'; '$'; '?']

let is_alphabetic c =
  'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z'

let rec tokenize' (s: string) i =
  if i = String.length s then []
  else
    match find_opt (fun x -> s.[i] = x) symbols with
      Some x -> Delim x :: tokenize' s (i + 1)
    | None ->
        let j = ref(i) in
        while !j < String.length s && is_alphabetic s.[!j] do
          j := !j + 1
        done;
        if i = !j then raise (TokenError (InvalidToken (sub s i 1)))
        else Ident (sub s i (!j - i)) :: tokenize' s !j

let tokenize s = tokenize' s 0
