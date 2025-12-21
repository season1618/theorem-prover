open Printf

type token
  = Delim of char
  | Ident of string

type term
  = Type
  | Kind
  | Const of string * term list
  | Var of string
  | App of term * term
  | Lam of string * term * term
  | Pi  of string * term * term

type token_error
  = InvalidToken of string

type syntax_error
  = Empty
  | UnexpectedToken of token * token
  | NoToken of token
  | InvalidVariable of string
  | NoVariable

exception TokenError of token_error

exception SyntaxError of syntax_error

let pp_token ppf = function
  | Delim c -> fprintf ppf "%c" c
  | Ident s -> fprintf ppf "%s" s

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

let rec pp_term ppf = function
  | Type -> fprintf ppf "*"
  | Kind -> fprintf ppf "□"
  | Const (name, args) -> fprintf ppf "%s[%a]" name pp_term_list args
  | Var x -> fprintf ppf "%s" x
  | App (t1, t2) -> fprintf ppf "(%a %a)" pp_term t1 pp_term t2
  | Lam (x, t, b) -> fprintf ppf "(λ %s : %a . %a)" x pp_term t pp_term b
  | Pi  (x, t, b) -> fprintf ppf "(Π %s : %a . %a)" x pp_term t pp_term b

and pp_term_list ppf = function
  | [] -> ()
  | term :: term_list ->
      fprintf ppf "%a" pp_term term;
      List.iter (fun term -> fprintf ppf ", %a" pp_term term) term_list
