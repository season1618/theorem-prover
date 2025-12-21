open Type

let var_count = ref(0)

let fresh_var () =
  var_count := !var_count + 1;
  "_" ^ string_of_int !var_count

let rec assign t y z =
  match t with
  | Type -> Type
  | Kind -> Kind
  | Const (name, args) -> Const (name, (List.map (fun t -> assign t y z) args))
  | Var x -> if x = y then Var z else Var x
  | App (t1, t2) -> App (assign t1 y z, assign t2 y z)
  | Lam (x, a, t) ->
      if x = y then Lam (x, assign a y z, t)
      else if x = z then let w = fresh_var () in assign (Lam (w, a, assign t x w)) y z
      else Lam (x, assign a y z, assign t y z)
  | Pi  (x, a, t) ->
      if x = y then Pi (x, assign a y z, t)
      else if x = z then let w = fresh_var () in assign (Pi (w, a, assign t x w)) y z
      else Pi (x, assign a y z, assign t y z)

let rec alpha_equiv t1 t2 =
  match (t1, t2) with
  | (Type, Type) | (Kind, Kind) -> true
  | (Const (name1, args1), Const (name2, args2)) -> name1 = name2 && List.for_all2 alpha_equiv args1 args2
  | (Var x1, Var x2) -> x1 = x2
  | (App (u1, v1), App (u2, v2)) -> alpha_equiv u1 u2 && alpha_equiv v1 v2
  | (Lam (x1, a1, t1), Lam (x2, a2, t2)) | (Pi (x1, a1, t1), Pi (x2, a2, t2)) ->
    alpha_equiv a1 a2 && let y = fresh_var () in alpha_equiv (assign t1 x1 y) (assign t2 x2 y)
  | (_, _) -> false
