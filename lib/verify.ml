open Type
open Error
open Lambda
open Value

open List
open Printf

let assert_sort t =
  match t with
  | Type | Kind -> ()
  | _ -> raise @@ DerivError (NotSort t)

let assert_same_name x1 x2 =
  if x1 = x2 then () else raise @@ DerivError (NotSameName (x1, x2))

let assert_alpha_equiv t1 t2 =
  if alpha_equiv t1 t2 then () else raise @@ DerivError (NotAlphaEquivalence (t1, t2))

let assert_alpha_beta_delta_equiv defs t1 t2 =
  if alpha_beta_delta_equiv defs t1 t2 then () else raise @@ DerivError (NotAlphaBetaDeltaEquiv (defs, t1, t2))

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

let assert_same_definition def1 def2 =
  let (_, name1, _, _) = def1 in
  let (_, name2, _, _) = def2 in
  if name1 = name2 then
    ()
  else
    raise @@ DerivError (DoNotMatchDefinition (def1, def2))

let assert_same_definitions defs1 defs2 =
  if length defs1 = length defs2 then
    iter2 assert_same_definition defs1 defs2
  else
    raise @@ DerivError (NotSameLengthDefinitions (defs1, defs2))

let rec assert_new_definition defs name =
  match defs with
  | [] -> ()
  | (_, name', _, _) as def :: _ when name' = name ->
      raise @@ DerivError (ConstAlreadyDefined (def, name))
  | _ :: defs -> assert_new_definition defs name

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
    | ("defpr" , [i; j; a]) -> DefPrim (int_of_string i, int_of_string j, a)
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
      assert_same_definitions defs1 defs2;
      assert_alpha_equiv_context ctx1 ctx2;
      assert_sort s;
      (defs1, (x, c) :: ctx1, a, b)
  | Form (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs1, ctx1, a1, s1), (defs2, (x, a2) :: ctx2, b, s2) ->
          assert_same_definitions defs1 defs2;
          assert_alpha_equiv_context ctx1 ctx2;
          assert_alpha_equiv a1 a2;
          assert_sort s1;
          assert_sort s2;
          (defs1, ctx1, Pi (x, a1, b), s2)
      | _, _ -> raise @@ DerivError EmptyContext)
  | App (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx, t1, Pi (x, a, b)), (defs', ctx', t2, a') ->
          assert_same_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          assert_alpha_equiv a a';
          (defs, ctx, App (t1, t2), subst b x t2)
      | (_, _, _, typ), _ -> raise @@ DerivError (NotPi typ))
  | Abs (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, (x, a) :: ctx, t, b), (defs', ctx', Pi (x', a', b'), s) ->
          assert_same_definitions defs defs';
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
          assert_same_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          assert_sort s;
          assert_alpha_beta_delta_equiv defs b1 b2;
          (defs, ctx, a, b2)
      )
  | Def (i, j, name) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx1, term1, type1), (defs', ctx2, term2, type2) ->
          assert_same_definitions defs defs';
          assert_new_definition defs name;
          let def = (ctx2, name, Some term2, type2) in
          (def :: defs, ctx1, term1, type1)
      )
  | DefPrim (i, j, name) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx1, term1, type1), (defs', ctx2, type2, s) ->
          assert_same_definitions defs defs';
          assert_new_definition defs name;
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
          assert_same_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          (u, v)
        ) js in
        let (arg_terms, arg_types) = split args in
        let (param_vars, param_types) = split (rev ctx2) in
        iter2 (fun param_type arg_type ->
          assert_alpha_equiv (subst_simul param_type (combine param_vars arg_terms)) arg_type
        ) param_types arg_types;
        (defs, ctx, Const (name, arg_terms), subst_simul typ (combine param_vars arg_terms))
      else
        raise @@ DerivError (NotTypeKind (typ, kind))

let verify derivs =
  let book = Vector.create ~dummy:([], [], Type, Kind) in
  iteri (fun i deriv ->
    (* printf "%d\n" i; *)
    try
      let time1 = Unix.gettimeofday () in
      Vector.push book (derive book deriv);
      let time2 = Unix.gettimeofday () in
      printf "%d %f\n" i (time2 -. time1);
    with
    | DerivError err ->
        printf "line %d\n" i;
        print_deriv_error book deriv err;
        exit 0
  ) derivs;
  book
