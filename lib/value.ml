open Type
open Util
open Lambda

open List

type value
  = Neut of neut
  | Lam of (value -> value) * value

and neut
  = Type
  | Kind
  | Const of string * value list
  | Var of string
  | App of neut * value
  | Pi of (value -> value) * value

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
      let (ctx, body, _) = find_const defs name in
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
  | Pi  (x, a, t) -> Neut (Pi ((fun v -> eval defs ((x, v) :: env) t), eval defs env a))

and apply v1 v2 =
  match v1 with
  | Neut n -> Neut (App (n, v2))
  | Lam (f, _) -> f v2

let rec readback value : term =
  match value with
  | Neut Type -> Type
  | Neut Kind -> Kind
  | Neut (Const (name, vals)) -> Const (name, map readback vals)
  | Neut (Var x) -> Var x
  | Neut (App (n, t)) -> App (readback (Neut n), readback t)
  | Neut (Pi (f, a)) -> let x = fresh_var () in Pi (x, readback a, readback (f (Neut (Var x))))
  | Lam (f, a) -> let x = fresh_var () in Lam (x, readback a, readback (f (Neut (Var x))))

let normalize_by_eval defs term =
  readback (eval defs [] term)

let rec equal v1 v2 =
  match (v1, v2) with
  | (Neut Type, Neut Type) | (Neut Kind, Neut Kind) -> true
  | (Neut (Const (name1, args1)), Neut (Const (name2, args2))) ->
      name1 = name2 && for_all2 equal args1 args2
  | (Neut (Var x1), Neut (Var x2)) -> x1 = x2
  | (Neut (App (n1, v1)), Neut (App (n2, v2))) ->
      equal (Neut n1) (Neut n2) && equal v1 v2
  | (Neut (Pi (f1, a1)), Neut (Pi (f2, a2))) | (Lam (f1, a1), Lam (f2, a2)) ->
      equal a1 a2 &&
      let x = fresh_var () in equal (f1 (Neut (Var x))) (f2 (Neut (Var x)))
  | (_, _) -> false
