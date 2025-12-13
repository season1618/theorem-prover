type token
  = Delim of char
  | Ident of string

type token_error
  = InvalidToken of string

exception TokenError of token_error

let pp_token ppf = function
  | Delim c -> Printf.fprintf ppf "%c" c
  | Ident s -> Printf.fprintf ppf "%s" s

let print_token token =
  match token with
    Delim c -> print_char c
  | Ident s -> print_string s

let rec print_token_list token_list =
  match token_list with
    [] -> ()
  | tok :: toks ->
      Printf.printf "%a " pp_token tok;
      print_token_list toks

let println_token_list token_list =
  print_token_list token_list;
  print_string "\n"
