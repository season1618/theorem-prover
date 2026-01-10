open Type
open Util

open List

(* y may be either a free variable or a binding variable in t *)
let rec rename t x y =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, (map (fun t -> rename t x y) args))
  | Var x' -> if x' = x then Var y else Var x'
  | App (t1, t2) -> App (rename t1 x y, rename t2 x y)
  | Lam (x', a, t) ->
      if x' = x then Lam (x', rename a x y, t)
      else if x' = y then let x'' = fresh_var () in rename (Lam (x'', a, rename t x' x'')) x y
      else Lam (x', rename a x y, rename t x y)
  | Pi  (x', a, t) ->
      if x' = x then Pi (x', rename a x y, t)
      else if x' = y then let x'' = fresh_var () in rename (Pi (x'', a, rename t x' x'')) x y
      else Pi (x', rename a x y, rename t x y)

(* y must be neither a free variable nor a binding variable in t *)
let rec rename_fresh t x y =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, (map (fun t -> rename_fresh t x y) args))
  | Var x' -> if x' = x then Var y else Var x'
  | App (t1, t2) -> App (rename_fresh t1 x y, rename_fresh t2 x y)
  | Lam (x', a, t) ->
      if x' = x then Lam (x', rename_fresh a x y, t)
      else Lam (x', rename_fresh a x y, rename_fresh t x y)
  | Pi  (x', a, t) ->
      if x' = x then Pi (x', rename_fresh a x y, t)
      else Pi (x', rename_fresh a x y, rename_fresh t x y)

let rec subst t x u =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, map (fun t -> subst t x u) args)
  | Var x' -> if x' = x then u else Var x'
  | App (t1, t2) -> App (subst t1 x u, subst t2 x u)
  | Lam (x', a, t) ->
      let x'' = fresh_var () in
      Lam (x'', subst a x u, subst (rename_fresh t x' x'') x u)
  | Pi  (x', a, t) ->
      let x'' = fresh_var () in
      Pi (x'', subst a x u, subst (rename_fresh t x' x'') x u)

let rec subst_simul t substs =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, map (fun t -> subst_simul t substs) args)
  | Var x' ->
      let rec subst_simul_var substs =
        match substs with
        | [] -> t
        | (x, u) :: _ when x' = x -> u
        | _ :: substs -> subst_simul_var substs
      in subst_simul_var substs
  | App (t1, t2) -> App (subst_simul t1 substs, subst_simul t2 substs)
  | Lam (x', a, t) ->
      let x'' = fresh_var () in
      Lam (x'', subst_simul a substs, subst_simul (rename_fresh t x' x'') substs)
  | Pi  (x', a, t) ->
      let x'' = fresh_var () in
      Pi (x'', subst_simul a substs, subst_simul (rename_fresh t x' x'') substs)

let subst_list t xs us =
  fold_left2 subst t xs us

let rec alpha_equiv t1 t2 =
  match (t1, t2) with
  | (Type, Type) | (Kind, Kind) -> true
  | (Const (name1, args1), Const (name2, args2)) ->
      name1 = name2 && length args1 = length args2 && for_all2 alpha_equiv args1 args2
  | (Var x1, Var x2) -> x1 = x2
  | (App (u1, v1), App (u2, v2)) -> alpha_equiv u1 u2 && alpha_equiv v1 v2
  | (Lam (x1, a1, t1), Lam (x2, a2, t2)) | (Pi (x1, a1, t1), Pi (x2, a2, t2)) ->
      alpha_equiv a1 a2 && let y = fresh_var () in alpha_equiv (rename_fresh t1 x1 y) (rename_fresh t2 x2 y)
  | (_, _) -> false

let rec find_const defs name =
  match defs with
  | [] -> raise @@ DerivError (UndefinedConst name)
  | (ctx, name', term, typ) :: _ when name' = name -> (ctx, term, typ)
  | _ :: defs -> find_const defs name

let rec normalize defs term =
  match term with
  | Const (name, args) ->
      let (ctx, body, _) = find_const defs name in
      let params = rev ctx in
      let args = map (normalize defs) args in
      if length params = length args then
        match body with
        | Some body ->
            let substs = map2 (fun (x, _) u -> (x, u)) params args in
            normalize defs (subst_simul body substs)
        | None -> Const (name, args)
      else
        raise @@ DerivError (NotSameLengthParamArg (name, ctx, args))
  | App (t1, t2) ->
      let t1 = normalize defs t1 in
      let t2 = normalize defs t2 in
      (match t1 with
      | Lam (x, _, b) -> normalize defs (subst b x t2)
      | _ -> App (t1, t2))
  | Lam (x, a, b) -> Lam (x, normalize defs a, normalize defs b)
  | Pi  (x, a, b) -> Pi  (x, normalize defs a, normalize defs b)
  | _ -> term
