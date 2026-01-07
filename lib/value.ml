open Type
open Util

open List

type value
  = Neut of neut
  | Lam of (value -> value) * value
  | Pi  of (value -> value) * value

and neut
  = Type
  | Kind
  | Const of string * value list
  | Var of string
  | Cons of neut * value

let rec find_var env name =
  match env with
  | [] -> Neut (Var name)
  | (name', value) :: _ when name' = name -> value
  | _ :: env -> find_var env name

let rec eval defs (env : (string * value) list) (term : term) : value =
  match term with
  | Type -> Neut Type
  | Kind -> Neut Kind
  | Const (name, args) ->
      let (ctx, body, _) = find_def defs name in
      let params = rev ctx in
      let vals = map (eval defs env) args in
      if length params = length args then
        match body with
        | Some body ->
            let substs = map2 (fun (x, _) u -> (x, u)) params vals in
            eval defs (rev_append substs env) body
        | None -> Neut (Const (name, vals))
      else
        raise @@ DerivError (NotSameLengthParamArg (name, ctx, args))
  | Var x -> find_var env x
  | App (t1, t2) -> apply (eval defs env t1) (eval defs env t2)
  | Lam (x, a, t) -> Lam ((fun v -> eval defs ((x, v) :: env) t), eval defs env a)
  | Pi  (x, a, t) -> Pi  ((fun v -> eval defs ((x, v) :: env) t), eval defs env a)

and apply v1 v2 =
  match v1 with
  | Neut n -> Neut (Cons (n, v2))
  | Lam (f, _) | Pi (f, _) -> f v2

let rec readback value : term =
  match value with
  | Neut Type -> Type
  | Neut Kind -> Kind
  | Neut (Const (name, vals)) -> Const (name, map readback vals)
  | Neut (Var x) -> Var x
  | Neut (Cons (n, t)) ->
      let t1 = readback (Neut n) in
      let t2 = readback t in
      App (t1, t2)
  | Lam (f, a) -> let x = fresh_var () in Lam (x, readback a, readback (f (Neut (Var x))))
  | Pi  (f, a) -> let x = fresh_var () in Pi  (x, readback a, readback (f (Neut (Var x))))

let normalize_by_eval defs term =
  readback (eval defs [] term)
