open Format
open List

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
type definition = context * string * term option * term
type definitions = definition list
type judgement = definitions * context * term * term
type deriv
  = Sort
  | Var of int * string
  | Weak of int * int * string
  | Form of int * int
  | App of int * int
  | Abs of int * int
  | Conv of int * int
  | Def of int * int * string
  | DefPrim of int * int * string
  | Inst of int * int list * int

type token_error
  = InvalidToken of string

type syntax_error
  = Empty
  | UnexpectedToken of token * token
  | NoToken of token
  | InvalidVariable of string
  | NoVariable

type type_error
  = KindHasNoType
  | VarUndef of string
  | NotPi of term
  | TypeMismatch of term * term

type deriv_error
  = NotSort of term
  | NotSameName of string * string
  | NotAlphaEquivalence of term * term
  | NotAlphaBetaDeltaEquiv of definitions * term * term
  | EmptyContext
  | NotSameLengthContext of context * context
  | NotSameLengthDefinitions of definitions * definitions
  | NotSameLengthParamArg of string * context * term list
  | ConstAlreadyDefined of definition * string
  | DoNotMatchDefinition of definition * definition
  | UndefinedConst of string
  | NotTypeKind of term * term
  | NotPi of term

exception TokenError of token_error

exception SyntaxError of syntax_error

exception TypeError of type_error

exception DerivError of deriv_error

let pp_sep ff () = fprintf ff ", "
let pp_list pp_elem = pp_print_list ~pp_sep:pp_sep pp_elem

let pp_token ff = function
  | Delim c -> fprintf ff "%c" c
  | Ident s -> fprintf ff "%s" s

let pp_tokens ff = function
  | [] -> ()
  | tokens -> fprintf ff "%a" (pp_list pp_token) tokens

let rec pp_term ff = function
  | Type -> fprintf ff "*"
  | Kind -> fprintf ff "□"
  | Const (name, args) -> fprintf ff "%s[%a]" name (pp_list pp_term) args
  | Var x -> fprintf ff "%s" x
  | App (t1, t2) -> fprintf ff "(%a %a)" pp_term t1 pp_term t2
  | Lam (x, t, b) -> fprintf ff "(λ %s : %a . %a)" x pp_term t pp_term b
  | Pi  (x, t, b) -> fprintf ff "(Π %s : %a . %a)" x pp_term t pp_term b

let pp_subst ff (x, term) =
  fprintf ff "%s := %a" x pp_term term

let pp_state ff (term, typ) =
  fprintf ff "%a : %a" pp_term term pp_term typ

let pp_decl ff (x, typ) =
  fprintf ff "%s : %a" x pp_term typ

let pp_ctx ff = function
  | [] -> fprintf ff "∅"
  | ctx -> fprintf ff "%a" (pp_list pp_decl) (rev ctx)

let pp_def ff (ctx, name, term, typ) =
  match term with
  | Some term -> fprintf ff "%a |> %s := %a : %a" pp_ctx ctx name pp_term term pp_term typ
  | None -> fprintf ff "%a |> %s : %a" pp_ctx ctx name pp_term typ

let pp_defs ff = function
  | [] -> fprintf ff "∅"
  | defs -> fprintf ff "%a" (pp_list pp_def) (rev defs)

let pp_consts ff = function
  | [] -> fprintf ff "∅"
  | defs -> fprintf ff "%a" (pp_list pp_print_string) (map (fun (_, name, _, _) -> name) (rev defs))

let pp_judge ff (defs, ctx, term, typ) =
  fprintf ff "%a ; %a |- %a : %a" pp_consts defs pp_ctx ctx pp_term term pp_term typ

let pp_judge_simp ff (_, _, term, typ) =
  fprintf ff ".. |- %a : %a" pp_term term pp_term typ

let pp_deriv ff deriv =
  match deriv with
  | Sort -> fprintf ff "sort"
  | Var (i, x) -> fprintf ff "var %d %s" i x
  | Weak (i, j, x) -> fprintf ff "weak %d %d %s" i j x
  | Form (i, j) -> fprintf ff "form %d %d" i j
  | App (i, j) -> fprintf ff "appl %d %d" i j
  | Abs (i, j) -> fprintf ff "abst %d %d" i j
  | Conv (i, j) -> fprintf ff "conv %d %d" i j
  | Def (i, j, c) -> fprintf ff "def %d %d %s" i j c
  | DefPrim (i, j, c) -> fprintf ff "defpr %d %d %s" i j c
  | Inst (i, js, k) ->
      let n = length js in
      fprintf ff "inst %d %d %a %d" i n (pp_print_list ~pp_sep:pp_print_space pp_print_int) js k

let print_derivs ff derivs =
  Vector.iteri (fun line deriv -> fprintf ff "%d %a\n" line pp_deriv deriv) derivs;
  fprintf ff "-1\n"

let print_book book = Vector.iteri (fun line judge -> printf "%d : %a\n" line pp_judge judge) book

let print_deriv book deriv =
  match deriv with
  | Sort -> ()
  | Var (i, _) ->
      printf "%a\n" pp_judge (Vector.get book i)
  | Weak (i, j, _) | Form (i, j) | App (i, j) | Abs (i, j) | Conv (i, j) | Def (i, j, _) | DefPrim (i, j, _) ->
      printf "%a %a\n" pp_judge (Vector.get book i) pp_judge (Vector.get book j)
  | Inst (i, js, k) ->
      let judge0 = Vector.get book i in
      let (defs, _, _, _) = judge0 in
      let (params, name, _, typ) as def = nth (rev defs) k in
      let args_judge = map (Vector.get book) js in
      let args_state = map (fun (_, _, term, typ) -> (term, typ)) args_judge in
      let args = map (fun (_, _, term, _) -> term) args_judge in

      let def_str = asprintf "%a" pp_def def in
      let premiss_str = asprintf "%a    .. |- %a"
        pp_judge_simp judge0
        (pp_list pp_state) args_state
      in
      let concl_str = asprintf ".. |- %a : %a[%a]"
        pp_term (Const (name, args))
        pp_term typ
        (pp_list pp_subst) (map2 (fun (x, _) u -> (x, u)) (rev params) args)
      in
      print_endline def_str;
      print_endline premiss_str;
      for _ = 0 to max (String.length premiss_str) (String.length concl_str) do
        printf "-"
      done;
      print_endline "";
      print_endline concl_str
