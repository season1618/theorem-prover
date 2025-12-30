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

type context = (string * term) list
type definition = context * string * term * term
type definitions = definition list
type judgement = definitions * context * term * term
type deriv
  = Sort
  | Var of int * string
  | Weak of int * int * string
  | Form of int * int

type token_error
  = InvalidToken of string

type syntax_error
  = Empty
  | UnexpectedToken of token * token
  | NoToken of token
  | InvalidVariable of string
  | NoVariable

type deriv_error
  = NotSort of term
  | NotSameName of string * string
  | NotAlphaEquivalence of term * term
  | EmptyContext
  | NotSameLengthContext of context * context
  | NotSameLengthDefinitions of definitions * definitions
  | NotSameLengthParamArg of string * context * term list
  | UndefinedConst of string

exception TokenError of token_error

exception SyntaxError of syntax_error

exception DerivError of deriv_error

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

let pp_ctx ppf = function
  | [] -> ()
  | (x, a) :: ctx ->
      List.iter (fun (x, a) -> fprintf ppf "%s:%a, " x pp_term a) (List.rev ctx);
      fprintf ppf "%s:%a" x pp_term a

let pp_def ppf (ctx, name, term, typ) =
  fprintf ppf "%a ; %s := %a : %a" pp_ctx ctx name pp_term term pp_term typ

let pp_defs ppf = function
  | [] -> ()
  | def :: defs ->
      List.iter (fprintf ppf "%a, " pp_def) (List.rev defs);
      fprintf ppf "%a" pp_def def

let pp_judge ppf (defs, ctx, term, typ) =
  fprintf ppf "%a ; %a |- %a : %a" pp_defs defs pp_ctx ctx pp_term term pp_term typ

let print_book book = Vector.iteri (fun line judge -> printf "%d : %a\n" line pp_judge judge) book
