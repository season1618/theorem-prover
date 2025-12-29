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

let assert_sort t =
  match t with
  | Type | Kind -> ()
  | _ -> raise @@ DerivError (NotSort t)

let assert_same_name x1 x2 =
  if x1 = x2 then () else raise @@ DerivError (NotSameName (x1, x2))

let assert_alpha_equiv t1 t2 =
  if alpha_equiv t1 t2 then () else raise @@ DerivError (NotAlphaEquivalence (t1, t2))

let assert_alpha_equiv_context ctx1 ctx2 =
  List.iter2 (fun (x1, t1) -> fun (x2, t2) ->
    if x1 = x2 then assert_alpha_equiv t1 t2
    else assert_same_name x1 x2
  ) ctx1 ctx2

let assert_alpha_equiv_definition def1 def2 =
  let (ctx1, a1, u1, v1) = def1 in
  let (ctx2, a2, u2, v2) = def2 in
  assert_alpha_equiv_context ctx1 ctx2;
  assert_same_name a1 a2;
  assert_alpha_equiv u1 u2;
  assert_alpha_equiv v1 v2

let assert_alpha_equiv_definitions defs1 defs2 =
  List.iter2 assert_alpha_equiv_definition defs1 defs2

let rec read_derivs () =
  let str = read_line () in
  let line, list = match String.split_on_char ' ' str with
    | line :: list -> (line, list)
    | [] -> raise @@ Failure "empty" in
  let line = int_of_string line in
  if line = -1 then
    []
  else
    let (rule, args) = match list with
      | rule :: args -> (rule, args)
      | [] -> raise @@ Failure str in
    (match (rule, args) with
    | ("sort", []) -> Sort
    | ("var", [i; x]) -> Var (int_of_string i, x)
    | ("weak", [i; j; x]) -> Weak (int_of_string i, int_of_string j, x)
    | ("form", [i; j]) -> Form (int_of_string i, int_of_string j)
    | _ -> raise @@ Failure ("rule : " ^ rule))
    :: read_derivs ()

let derive book deriv =
  match deriv with
  | Sort -> ([], [], Type, Kind)
  | Var (i, x) ->
      let (defs, ctx, a, s) = Vector.get book i in
      assert_sort s;
      (defs, (x, a) :: ctx, Var x, a)
  | Weak (i, j, x) ->
      let (defs1, ctx1, a, b) = Vector.get book i in
      let (defs2, ctx2, c, s) = Vector.get book j in
      assert_alpha_equiv_definitions defs1 defs2;
      assert_alpha_equiv_context ctx1 ctx2;
      assert_sort s;
      (defs1, (x, c) :: ctx1, a, b)
  | Form (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs1, ctx1, a1, s1), (defs2, (x, a2) :: ctx2, b, s2) ->
          assert_alpha_equiv_definitions defs1 defs2;
          assert_alpha_equiv_context ctx1 ctx2;
          assert_alpha_equiv a1 a2;
          assert_sort s1;
          assert_sort s2;
          (defs1, ctx1, Pi (x, a1, b), s2)
      | _, _ -> raise @@ DerivError EmptyContext)

let verify () =
  let derivs = read_derivs () in

  let book = Vector.create ~dummy:([], [], Type, Kind) in
  List.iter (fun deriv -> Vector.push book (derive book deriv)) derivs;
  book
