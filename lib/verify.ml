open Type
open Error
open Lambda
open Value
open Parser

open List
open Format

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

let rec assert_new_var ctx name =
  match ctx with
  | [] -> ()
  | (name', _) :: _ when name' = name ->
      raise @@ DerivError (VarAlreadyDefined (ctx, name))
  | _ :: ctx -> assert_new_var ctx name

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

let rec read_defs file =
  match input_line file with
  | "END" -> []
  | "def2" ->
      let n = int_of_string (input_line file) in
      let ctx = rev @@ init n (fun _ ->
        let var = input_line file in
        let (typ, _) = parse (input_line file) in
        (var, typ)
      ) in
      let name = input_line file in
      let body = let body = input_line file in
        if body = "#" then
          None
        else
          let (body, _) = parse body in
          Some body
        in
      let (typ, _) = parse (input_line file) in
      ignore @@ input_line file;
      (ctx, name, body, typ) :: read_defs file
  | "" -> read_defs file
  | str -> raise @@ Failure str

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

let rec infer_type defs ctx term =
  match term with
  | Type -> Kind
  | Kind -> raise @@ TypeError KindHasNoType
  | Const (name, args) ->
      let (ctx, _, typ) = find_const defs name in
      let used = fst (split ctx) in
      subst_symb used typ (map2 (fun (x, _) arg -> (x, arg)) (rev ctx) args)
  | Var x -> find_var ctx x
  | App (term1, term2) ->
      let used = fst (split ctx) in
      let type1 = normalize_symb used defs (infer_type defs ctx term1) in
      let type2 = infer_type defs ctx term2 in
      (match (type1, type2) with
      | (Pi (x, a, b), a') ->
          if alpha_beta_delta_equiv defs a a' then
            subst_symb used b [(x, term2)]
          else
            raise @@ TypeError (TypeMismatchApp (term1, type1, term2, type2, a, a'));
      | (_, _) -> raise @@ TypeError (NotPi type1)
      )
  | Lam (x, a, t) ->
      let b = infer_type defs ((x, a) :: ctx) t in
      Pi (x, a, b)
  | Pi (x, a, b) ->
      let s = (infer_type defs ((x, a) :: ctx) b) in
      if s = Type || s = Kind then
        s
      else
        raise @@ TypeError (NotSort (term, s))

let check_definition defs (ctx, _, term, expected) =
  match term with
  | Some term ->
      let infered = infer_type defs ctx term in
      if alpha_beta_delta_equiv defs expected infered then
        ()
      else
        raise @@ TypeError (TypeMismatch (expected, infered))
  | None -> ()

let rec check_definitions def_list defs =
  match def_list with
  | [] -> ()
  | (def :: def_list) ->
      (try check_definition defs def with
      | TypeError err ->
          print_type_error err;
          printf "    %a\n" pp_def def;
          exit 0
      );
      check_definitions def_list (def :: defs)

let check_definitions def_list =
  check_definitions def_list []

let fresh_term ctx (x, t) =
  let x' = fresh_char (fst (split ctx)) (free_bind_var [t]) in
  let t' = rename_fresh t x x' in
  (x', t')

let reg_deriv book deriv =
  Vector.push book deriv;
  Vector.length book - 1

let rec derive_type_noctx book cache defs =
  match defs with
  | [] -> Sort
  | (ctx, name, term, typ) as def :: defs ->
      try
        (match term with
        | Some term ->
            let (deriv1, _) = derive_term_memo book cache (defs, [], Type) in
            let deriv2 = derive_term_type book cache (defs, ctx, term, typ) in
            Def (deriv1, deriv2, name)
        | None ->
            let (deriv1, _) = derive_term_memo book cache (defs, [], Type) in
            let (deriv2, _) = derive_term_memo book cache (defs, ctx, typ) in
            DefPrim (deriv1, deriv2, name)
        )
      with
      | TypeError err ->
          print_type_error err;
          printf "    %a\n" pp_def def;
          exit 0

and derive_type book cache (defs, ctx) =
  match ctx with
  | [] -> derive_type_noctx book cache defs
  | (x, a) :: ctx ->
      let (deriv1, _) = derive_term_memo book cache (defs, ctx, Type) in
      let (deriv2, _) = derive_term_memo book cache (defs, ctx, a) in
      Weak (deriv1, deriv2, x)

and derive_var book cache (defs, ctx, x) =
  match ctx with
  | [] -> raise @@ TypeError (VarUndef x)
  | (x', a) :: ctx when x' = x ->
      let (deriv, _) = derive_term_memo book cache (defs, ctx, a) in
      (Var (deriv, x), a)
  | (y, b) :: ctx ->
      let (deriv1, a) = derive_term_memo book cache (defs, ctx, Var x) in
      let (deriv2, _) = derive_term_memo book cache (defs, ctx, b) in
      (Weak (deriv1, deriv2, y), a)

and derive_term book cache (defs, ctx, term) =
  let used = fst (split ctx) in
  match term with
  | Type -> (derive_type book cache (defs, ctx), Kind)
  | Kind -> raise @@ TypeError KindHasNoType
  | Const (name, args) ->
      let (ctx2, _, ret_type) = find_const defs name in
      let (params, param_types) = split (rev ctx2) in
      let def_idx = Option.get @@ find_index (fun (_, name', _, _) -> name' = name) (rev defs) in

      let substs = combine params args in
      let arg_types = map (fun param_type -> subst_symb used param_type substs) param_types in
      let res_type = subst_symb used ret_type substs in

      let (deriv0, _) = derive_term_memo book cache (defs, ctx, Type) in
      let derivs = map2 (fun arg typ -> derive_term_type book cache (defs, ctx, arg, typ)) args arg_types in
      (Inst (deriv0, derivs, def_idx), res_type)
  | Var x -> derive_var book cache (defs, ctx, x)
  | App (t1, t2) ->
      let (deriv1, typ) = derive_term_norm book cache (defs, ctx, t1) in
      let (deriv2, _) = derive_term_norm book cache (defs, ctx, t2) in
      (match typ with
      | Pi (x, _, b) -> (App (deriv1, deriv2), subst_symb used b [(x, t2)])
      | _ -> raise @@ TypeError (NotPi typ)
      )
  | Lam (x, a, t) ->
      let (x, t) = if mem x (fst (split ctx)) then fresh_term ctx (x, t) else (x, t) in
      let (deriv1, b) = derive_term_memo book cache (defs, (x, a) :: ctx, t) in
      let (deriv2, _) = derive_term_memo book cache (defs, ctx, Pi (x, a, b)) in
      (Abs (deriv1, deriv2), Pi (x, a, b))
  | Pi (x, a, b) ->
      let (x, b) = if mem x (fst (split ctx)) then fresh_term ctx (x, b) else (x, b) in
      let (deriv1, _) = derive_term_norm book cache (defs, ctx, a) in
      let (deriv2, s) = derive_term_norm book cache (defs, ((x, a) :: ctx), b) in
      (Form (deriv1, deriv2), s)

and derive_term_norm book cache (defs, ctx, term) =
  let used = fst (split ctx) in
  let typ = normalize_symb used defs (infer_type defs ctx term) in
  if typ = Kind then
    derive_term_memo book cache (defs, ctx, term)
  else
    let (deriv1, _) = derive_term_memo book cache (defs, ctx, term) in
    let (deriv2, _) = derive_term_memo book cache (defs, ctx, typ) in
    (reg_deriv book (Conv (deriv1, deriv2)), typ)

and derive_term_type book cache (defs, ctx, term, typ) : int =
  if typ = Kind then
    fst @@ derive_term_memo book cache (defs, ctx, term)
  else
    let (deriv1, _) = derive_term_memo book cache (defs, ctx, term) in
    let (deriv2, _) = derive_term_memo book cache (defs, ctx, typ) in
    reg_deriv book (Conv (deriv1, deriv2))

and derive_term_memo book cache (defs, ctx, term) =
  match Hashtbl.find_opt cache (defs, ctx, term) with
  | Some (id, typ) -> (id, typ)
  | None ->
      let (deriv, typ) = derive_term book cache (defs, ctx, term) in
      let id = reg_deriv book deriv in
      Hashtbl.add cache (defs, ctx, term) (id, typ);
      (id, typ)

and gen_derivs def_list =
  let book = Vector.create ~dummy:Sort in
  let cache = Hashtbl.create ~random:false 0 in
  ignore @@ derive_term_memo book cache (rev def_list, [], Type);
  book

let verify_deriv book deriv =
  match deriv with
  | Sort -> ([], [], Type, Kind)
  | Var (i, x) ->
      let (defs, ctx, a, s) = Vector.get book i in
      assert_sort s;
      assert_new_var ctx x;
      (defs, (x, a) :: ctx, Var x, a)
  | Weak (i, j, x) ->
      let (defs, ctx, a, b) = Vector.get book i in
      let (defs', ctx', c, s) = Vector.get book j in
      assert_same_definitions defs defs';
      assert_alpha_equiv_context ctx ctx';
      assert_sort s;
      assert_new_var ctx x;
      (defs, (x, c) :: ctx, a, b)
  | Form (i, j) ->
      (match (Vector.get book i, Vector.get book j) with
      | (defs, ctx, a, s1), (defs', (x, a') :: ctx', b, s2) ->
          assert_same_definitions defs defs';
          assert_alpha_equiv_context ctx ctx';
          assert_alpha_equiv a a';
          assert_sort s1;
          assert_sort s2;
          (defs, ctx, Pi (x, a, b), s2)
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

let verify_derivs derivs =
  let book = Vector.create ~dummy:([], [], Type, Kind) in
  iteri (fun i deriv ->
    (* printf "%d\n" i; *)
    try
      (* let time1 = Unix.gettimeofday () in *)
      Vector.push book (verify_deriv book deriv);
      (* let time2 = Unix.gettimeofday () in *)
      (* printf "%d %f\n" i (time2 -. time1); *)
    with
    | DerivError err ->
        printf "line %d\n" i;
        print_deriv_error book deriv err;
        exit 0
  ) derivs;
  book
