type token
  = Delim of char
  | Ident of string

let print_token token =
  match token with
    Delim c -> print_char c
  | Ident s -> print_string s

let rec print_token_list token_list =
  match token_list with
    [] -> ()
  | tok :: toks ->
      print_token tok;
      print_string " ";
      print_token_list toks

let println_token_list token_list =
  print_token_list token_list;
  print_string "\n"
