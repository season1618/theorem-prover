open Type
open Error
open Util

open List

let rec free_bind_var set term =
  match term with
  | Type | Kind -> ()
  | Const (_, args) -> iter (free_bind_var set) args
  | Var x -> Hashset.add set x
  | App (t1, t2) ->
      free_bind_var set t1;
      free_bind_var set t2
  | Lam (x, a, t) | Pi (x, a, t) ->
      Hashset.add set x;
      free_bind_var set a;
      free_bind_var set t
let free_bind_var terms =
  let set = Hashset.create 0 in
  iter (free_bind_var set) terms;
  set

let rec fresh_char used set c =
  if not @@ Hashset.mem set (Char.escaped c) && not @@ mem (Char.escaped c) used then
    c
  else if c = 'z' then
    raise @@ Failure "no valid symbol"
  else
    fresh_char used set (Char.chr (Char.code c + 1))
let fresh_char used set = Char.escaped @@ fresh_char used set 'a'

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

let rec subst_var x substs : term =
  match substs with
  | [] -> Var x
  | (x', u) :: _ when x' = x -> u
  | _ :: substs -> subst_var x substs

let rec subst t substs =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, map (fun t -> subst t substs) args)
  | Var x -> subst_var x substs
  | App (t1, t2) -> App (subst t1 substs, subst t2 substs)
  | Lam (x', a, t) ->
      let x'' = fresh_var () in
      Lam (x'', subst a substs, subst (rename_fresh t x' x'') substs)
  | Pi  (x', a, t) ->
      let x'' = fresh_var () in
      Pi (x'', subst a substs, subst (rename_fresh t x' x'') substs)

let rec subst2 used t substs =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, map (fun t -> subst2 used t substs) args)
  | Var x -> subst_var x substs
  | App (t1, t2) -> App (subst2 used t1 substs, subst2 used t2 substs)
  | Lam (x', a, t) ->
      let vars = free_bind_var (t :: concat_map (fun (x, u) -> [(Var x : term); u]) substs) in
      let x'' = fresh_char used vars in
      Lam (x'', subst2 used a substs, subst2 (x'' :: used) (rename_fresh t x' x'') substs)
  | Pi  (x', a, t) ->
      let vars = free_bind_var (t :: concat_map (fun (x, u) -> [(Var x : term); u]) substs) in
      let x'' = fresh_char used vars in
      Pi  (x'', subst2 used a substs, subst2 (x'' :: used) (rename_fresh t x' x'') substs)

let rec subst_by_eval env term =
  match term with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, map (subst_by_eval env) args)
  | Var x -> subst_var x env
  | App (t1, t2) -> App (subst_by_eval env t1, subst_by_eval env t2)
  | Lam (x, a, t) ->
      let x' = fresh_var () in
      Lam (x', subst_by_eval env a, subst_by_eval ((x, Var x') :: env) t)
  | Pi  (x, a, t) ->
      let x' = fresh_var () in
      Pi (x', subst_by_eval env a, subst_by_eval ((x, Var x') :: env) t)
let subst_by_eval term substs = subst_by_eval substs term

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

let rec find_var ctx name =
  match ctx with
  | [] -> raise @@ TypeError (VarUndef name)
  | (name', typ) :: _ when name' = name -> typ
  | _ :: ctx -> find_var ctx name

let rec find_var2 env name =
  match env with
  | [] -> name
  | (name', var) :: _ when name' = name -> var
  | _ :: env -> find_var2 env name

let delta_reduce defs name args =
  let (ctx, body, _) = find_const defs name in
  let params = rev ctx in
  match body with
  | Some body ->
      let substs = map2 (fun (x, _) u -> (x, u)) params args in
      Some (subst_by_eval body substs)
  | None -> None

let rec reduce_head defs term =
  match term with
  | Const (name, args) -> delta_reduce defs name args
  | App (Lam (x, _, b), t2) -> Some (subst_by_eval b [(x, t2)])
  | App (t1, t2) ->
      let t1 = reduce_head defs t1 in
      (match t1 with
      | Some (Lam (x, _, b)) -> Some (subst_by_eval b [(x, t2)])
      | Some t1 -> Some (App (t1, t2))
      | None -> None
      )
  | _ -> None

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
            normalize defs (subst body substs)
        | None -> Const (name, args)
      else
        raise @@ DerivError (NotSameLengthParamArg (name, ctx, args))
  | App (t1, t2) ->
      let t1 = normalize defs t1 in
      let t2 = normalize defs t2 in
      (match t1 with
      | Lam (x, _, b) -> normalize defs (subst b [(x, t2)])
      | _ -> App (t1, t2))
  | Lam (x, a, b) -> Lam (x, normalize defs a, normalize defs b)
  | Pi  (x, a, b) -> Pi  (x, normalize defs a, normalize defs b)
  | _ -> term

let rec normalize2 used defs term =
  match term with
  | Const (name, args) ->
      let (ctx, body, _) = find_const defs name in
      let params = rev ctx in
      let args = map (normalize2 used defs) args in
      if length params = length args then
        match body with
        | Some body ->
            let substs = map2 (fun (x, _) u -> (x, u)) params args in
            normalize2 used defs (subst2 used body substs)
        | None -> Const (name, args)
      else
        raise @@ DerivError (NotSameLengthParamArg (name, ctx, args))
  | App (t1, t2) ->
      let t1 = normalize2 used defs t1 in
      let t2 = normalize2 used defs t2 in
      (match t1 with
      | Lam (x, _, b) -> normalize2 used defs (subst2 used b [(x, t2)])
      | _ -> App (t1, t2))
  | Lam (x, a, b) -> Lam (x, normalize2 used defs a, normalize2 (x :: used) defs b)
  | Pi  (x, a, b) -> Pi  (x, normalize2 used defs a, normalize2 (x :: used) defs b)
  | _ -> term

let rec alpha_beta_delta_equiv defs env1 env2 t1 t2 =
  match (t1, t2) with
  | (Type, Type) | (Kind, Kind) -> true
  | (Const (name, args1), Const (name', args2)) when name = name' ->
      if for_all2 (alpha_beta_delta_equiv defs env1 env2) args1 args2 then
        true
      else
        (match (reduce_head defs t1, reduce_head defs t2) with
        | (Some t1, Some t2) -> alpha_beta_delta_equiv defs env1 env2 t1 t2
        | (Some t1, None) -> alpha_beta_delta_equiv defs env1 env2 t1 t2
        | (None, Some t2) -> alpha_beta_delta_equiv defs env1 env2 t1 t2
        | (None, None) -> false
        )
  | (Var x1, Var x2) -> find_var2 env1 x1 = find_var2 env2 x2
  | (App (u1, v1), App (u2, v2)) ->
      if alpha_beta_delta_equiv defs env1 env2 u1 u2 && alpha_beta_delta_equiv defs env1 env2 v1 v2 then
        true
      else
        (match (reduce_head defs t1, reduce_head defs t2) with
        | (Some t1, Some t2) -> alpha_beta_delta_equiv defs env1 env2 t1 t2
        | (Some t1, None) -> alpha_beta_delta_equiv defs env1 env2 t1 t2
        | (None, Some t2) -> alpha_beta_delta_equiv defs env1 env2 t1 t2
        | (None, None) -> false
        )
  | (Lam (x1, a1, t1), Lam (x2, a2, t2)) | (Pi (x1, a1, t1), Pi (x2, a2, t2)) ->
      alpha_beta_delta_equiv defs env1 env2 a1 a2 &&
      let x = fresh_var () in
      alpha_beta_delta_equiv defs ((x1, x) :: env1) ((x2, x) :: env2) t1 t2
  | (Const (_, _), Const (_, _)) | (Const (_, _), App (_, _)) | (App (_, _), Const (_, _)) ->
      (match reduce_head defs t1 with
      | Some t1 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None ->
          (match reduce_head defs t2 with
          | Some t2 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
          | None -> false
          )
      )
  | (Const (_, _), _) | (App (_, _), _) ->
      (match reduce_head defs t1 with
      | Some t1 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None -> false
      )
  | (_, Const (_, _)) | (_, App (_, _)) ->
      (match reduce_head defs t2 with
      | Some t2 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None -> false
      )
  | (_, _) -> false  
let alpha_beta_delta_equiv defs t1 t2 =
  alpha_beta_delta_equiv defs [] [] t1 t2

