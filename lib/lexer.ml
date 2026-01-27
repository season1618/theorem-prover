open Type
open Error

open String
open List

let symbols = ['('; ')'; '['; ']'; ','; '.'; ':'; '*'; '@'; '%'; '$'; '?']

let is_alphanumeric_ c =
  'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || '0' <= c && c <= '9' || c = '_' || c = '.'

let rec tokenize' (s: string) i =
  if i = String.length s then []
  else
    match find_opt (fun x -> s.[i] = x) symbols with
      Some x -> Delim x :: tokenize' s (i + 1)
    | None ->
        let j = ref(i) in
        while !j < String.length s && is_alphanumeric_ s.[!j] do
          j := !j + 1
        done;
        if i = !j then raise (TokenError (InvalidToken (sub s i 1)))
        else Ident (sub s i (!j - i)) :: tokenize' s !j

let tokenize s =
  try tokenize' s 0 with
  | TokenError err ->
      Format.printf "Token Error: ";
      (match err with
      | InvalidToken token -> Format.printf "invalid token '%s'\n" token);
      exit 0
