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

let rec size (term : term) =
  match term with
  | Type | Kind | Var _ -> 1
  | Const (_, args) -> fold_left (+) 1 (map size args)
  | App (t1, t2) | Lam (_, t1, t2) | Pi (_, t1, t2) -> size t1 + size t2 + 1

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

let rec alpha_beta_delta_equiv defs env1 env2 (t1 : term) (t2 : term) =
  Format.printf "%a\n" pp_term t1;
  Format.printf "%a\n" pp_term t2;
  Format.print_newline ();
  match (t1, t2) with
  | (Type, Type) | (Kind, Kind) -> true
  | (Const (name, args1), Const (name', args2)) when name = name' ->
      if for_all2 (alpha_beta_delta_equiv defs env1 env2) args1 args2 then
        true
      else
        equal (eval defs env1 t1) (eval defs env2 t2)
  | (Var x1, Var x2) -> find_var env1 x1 = find_var env2 x2
  | (App (u1, v1), App (u2, v2)) ->
      if alpha_beta_delta_equiv defs env1 env2 u1 u2 && alpha_beta_delta_equiv defs env1 env2 v1 v2 then
        true
      else
        equal (eval defs env1 t1) (eval defs env2 t2)
  | (Lam (x1, a1, t1), Lam (x2, a2, t2)) | (Pi (x1, a1, t1), Pi (x2, a2, t2)) ->
      alpha_beta_delta_equiv defs env1 env2 a1 a2 &&
      let x = Neut (Var (fresh_var ())) in
      alpha_beta_delta_equiv defs ((x1, x) :: env1) ((x2, x) :: env2) t1 t2
  | (Const (_, _), App (Lam (x, _, u), v)) ->
      alpha_beta_delta_equiv defs env1 env2 t1 (subst_by_eval u [(x, v)])
  | (App (Lam (x, _, u), v), Const (_, _)) ->
      alpha_beta_delta_equiv defs env1 env2 (subst_by_eval u [(x, v)]) t2
  | (Const (name, args), App (Const(_, _), _)) when size t1 < size t2 ->
      (match delta_reduce defs name args with
      | Some t1 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None -> equal (eval defs env1 t1) (eval defs env2 t2)
      ) 
  | (Const (_, _), App (Const (name, args), v)) ->
      (match delta_reduce defs name args with
      | Some u -> alpha_beta_delta_equiv defs env1 env2 t1 (App (u, v))
      | None -> equal (eval defs env1 t1) (eval defs env2 t2)
      )
  | (App (Const(_, _), _), Const (name, args)) when size t1 > size t2 ->
      (match delta_reduce defs name args with
      | Some t2 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None -> equal (eval defs env1 t1) (eval defs env2 t2)
      )
  | (App (Const (name, args), v), Const (_, _)) ->
      (match delta_reduce defs name args with
      | Some u -> alpha_beta_delta_equiv defs env1 env2 (App (u, v)) t2
      | None -> equal (eval defs env1 t1) (eval defs env2 t2)
      )
  | (Const (name, args) as t1, t2) ->
      (match delta_reduce defs name args with
      | Some t1 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None -> equal (eval defs env1 t1) (eval defs env2 t2)
      )
  | (t1, (Const (name, args) as t2)) ->
      (match delta_reduce defs name args with
      | Some t2 -> alpha_beta_delta_equiv defs env1 env2 t1 t2
      | None -> equal (eval defs env1 t1) (eval defs env2 t2)
      )
  | (App (_, _), _) | (_, App (_, _)) ->
      equal (eval defs env1 t1) (eval defs env2 t2)
  | (_, _) ->
      equal (eval defs env1 t1) (eval defs env2 t2)

let alpha_beta_delta_equiv defs t1 t2 =
  let time1 = Unix.gettimeofday () in
  let res = alpha_beta_delta_equiv defs [] [] t1 t2 in
  let time2 = Unix.gettimeofday () in

  (if time2 -. time1 > 1.0 then
    (Format.printf "1 : %d\n" (size t1);
    Format.printf "2 : %d\n" (size t2);
    Format.printf "1 : %a\n" pp_term t1;
    Format.printf "2 : %a\n" pp_term t2;
    Format.printf "%f\n" (time2 -. time1);
    Format.print_flush ())
  );
  res
