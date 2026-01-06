open Type
open Error

open List
open Printf

let var_count = ref(0)

let fresh_var () =
  var_count := !var_count + 1;
  "_" ^ string_of_int !var_count

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

let rec find_def defs name =
  match defs with
  | [] -> raise @@ DerivError (UndefinedConst name)
  | (ctx, name', term, typ) :: _ when name' = name -> (ctx, term, typ)
  | _ :: defs -> find_def defs name

let rec beta_delta_reduction defs term =
  match term with
  | Const (name, args) ->
      let (ctx, body, _) = find_def defs name in
      let params = rev ctx in
      let args = map (beta_delta_reduction defs) args in
      if length params = length args then
        match body with
        | Some body ->
            let substs = map2 (fun (x, _) u -> (x, u)) params args in
            beta_delta_reduction defs (subst_simul body substs)
        | None -> Const (name, args)
      else
        raise @@ DerivError (NotSameLengthParamArg (name, ctx, args))
  | App (t1, t2) ->
      let t1 = beta_delta_reduction defs t1 in
      let t2 = beta_delta_reduction defs t2 in
      (match t1 with
      | Lam (x, _, b) -> beta_delta_reduction defs (subst b x t2)
      | _ -> App (t1, t2))
  | Lam (x, a, b) -> Lam (x, beta_delta_reduction defs a, beta_delta_reduction defs b)
  | Pi  (x, a, b) -> Pi  (x, beta_delta_reduction defs a, beta_delta_reduction defs b)
  | _ -> term

let assert_sort t =
  match t with
  | Type | Kind -> ()
  | _ -> raise @@ DerivError (NotSort t)

let assert_same_name x1 x2 =
  if x1 = x2 then () else raise @@ DerivError (NotSameName (x1, x2))

let assert_alpha_equiv t1 t2 =
  if alpha_equiv t1 t2 then () else raise @@ DerivError (NotAlphaEquivalence (t1, t2))

let assert_alpha_equiv_context ctx1 ctx2 =
  if length ctx1 = length ctx2 then
    iter2 (fun (x1, t1) -> fun (x2, t2) ->
      if x1 = x2 then assert_alpha_equiv t1 t2
      else assert_same_name x1 x2
    ) ctx1 ctx2
  else
    raise @@ DerivError (NotSameLengthContext (ctx1, ctx2))

let assert_alpha_equiv_definition def1 def2 =
  let (ctx1, a1, u1, v1) = def1 in
  let (ctx2, a2, u2, v2) = def2 in
  assert_alpha_equiv_context ctx1 ctx2;
  assert_same_name a1 a2;
  (match (u1, u2) with
  | Some u1, Some u2 -> assert_alpha_equiv u1 u2
  | None, None -> ()
  | _ -> raise @@ DerivError (DoNotMatchDefinition (def1, def2)));
  assert_alpha_equiv v1 v2

let assert_alpha_equiv_definitions defs1 defs2 =
  if length defs1 = length defs2 then
    iter2 assert_alpha_equiv_definition defs1 defs2
  else
    raise @@ DerivError (NotSameLengthDefinitions (defs1, defs2))

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
    | ("var" , [i; x]) -> Var (int_of_string i, x)
    | ("weak", [i; j; x]) -> Weak (int_of_string i, int_of_string j, x)
    | ("form", [i; j]) -> Form (int_of_string i, int_of_string j)
    | ("appl", [i; j]) -> App (int_of_string i, int_of_string j)
    | ("abst", [i; j]) -> Abs (int_of_string i, int_of_string j)
    | ("conv", [i; j]) -> Conv (int_of_string i, int_of_string j)
    | ("def" , [i; j; a]) -> Def (int_of_string i, int_of_string j, a)
    | ("defpr" , [i; j; a]) -> Def (int_of_string i, int_of_string j, a)
    | ("inst", i :: n :: ks) ->
        let i = int_of_string i in
        let n = int_of_string n in
        let k = int_of_string @@ nth ks n in
        let js = init n (fun i -> int_of_string (nth ks i)) in
        Inst (i, js, k)
    | _ -> raise @@ Failure ("invalid rule : " ^ rule))
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
  | App (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx, t1, Pi (x, a, b)), (defs', ctx', t2, a') ->
          assert_alpha_equiv_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          assert_alpha_equiv a a';
          (defs, ctx, App (t1, t2), subst b x t2)
      | (_, _, _, typ), _ -> raise @@ DerivError (NotPi typ))
  | Abs (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, (x, a) :: ctx, t, b), (defs', ctx', Pi (x', a', b'), s) ->
          assert_alpha_equiv_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          assert_same_name x x';
          assert_alpha_equiv a a';
          assert_alpha_equiv b b';
          assert_sort s;
          (defs, ctx, Lam (x, a, t), Pi (x, a, b))
      | (_, _ :: _, _, _), (_, _, term, _) -> raise @@ DerivError (NotPi term)
      | (_, [], _, _), _ -> raise @@ DerivError (EmptyContext)
      )
  | Conv (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx, a, b1), (defs', ctx', b2, s) ->
          assert_alpha_equiv_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          assert_sort s;
          assert_alpha_equiv (beta_delta_reduction defs b1) (beta_delta_reduction defs b2);
          (defs, ctx, a, b2)
      )
  | Def (i, j, name) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx1, term1, type1), (defs', ctx2, term2, type2) ->
          assert_alpha_equiv_definitions defs defs';
          let def = (ctx2, name, Some term2, type2) in
          Format.printf "%a\n" pp_def def;
          (def :: defs, ctx1, term1, type1)
      )
  | DefPrim (i, j, name) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx1, term1, type1), (defs', ctx2, type2, s) ->
          assert_alpha_equiv_definitions defs defs';
          assert_sort s;
          let def = (ctx2, name, None, type2) in
          (def :: defs, ctx1, term1, type1)
      )
  | Inst (i, js, k) ->
      let (defs, ctx, typ, kind) = Vector.get book i in
      if typ = Type && kind = Kind then
        let (ctx2, name, _, typ) = nth (rev defs) k in
        let args = map (fun j ->
          let (defs', ctx', u, v) = Vector.get book j in
          assert_alpha_equiv_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          (u, v)
        ) js in
        let (arg_terms, arg_types) = split args in
        let (param_vars, param_types) = split (rev ctx2) in
        iter2 (fun param_type -> fun arg_type ->
          assert_alpha_equiv (subst_list param_type param_vars arg_terms) arg_type
        ) param_types arg_types;
        (defs, ctx, Const (name, arg_terms), subst_list typ param_vars arg_terms)
      else
        raise @@ DerivError (NotTypeKind (typ, kind))

let verify () =
  let derivs = read_derivs () in

  let book = Vector.create ~dummy:([], [], Type, Kind) in
  iteri (fun i deriv ->
    try Vector.push book (derive book deriv) with
    | DerivError err ->
        printf "line %d\n" i;
        print_deriv_error book deriv err;
        exit 0
  ) derivs;
  book
