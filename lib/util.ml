open Type

let var_count = ref(0)

let fresh_var () =
  var_count := !var_count + 1;
  "_" ^ string_of_int !var_count

let rec find_def defs name =
  match defs with
  | [] -> raise @@ DerivError (UndefinedConst name)
  | (ctx, name', term, typ) :: _ when name' = name -> (ctx, term, typ)
  | _ :: defs -> find_def defs name
