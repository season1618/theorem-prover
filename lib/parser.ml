open Type

open String

let parse_var token_list =
  match token_list with
  | Ident name :: rest when length name = 1 -> (name.[0], rest)
  | Ident name :: _ -> raise (SyntaxError (InvalidVariable name))
  | Delim _ :: _ | [] -> raise (SyntaxError NoVariable)

let parse_token token token_list =
  match token_list with
  | head :: tail -> if head = token
      then (head, tail)
      else raise (SyntaxError (UnexpectedToken (token, head)))
  | [] -> raise (SyntaxError (NoToken token))

let parse_token_if token token_list =
  match token_list with
  | head :: tail when head = token -> Some (head, tail)
  | _ -> None

let rec parse_term token_list =
  match token_list with
  | [] -> raise (SyntaxError Empty)
  | head :: tail ->
      (match head with
      | Delim '*' -> (Star, tail)
      | Delim '@' -> (Sort, tail)
      | Delim '%' ->
          let (term1, tail) = parse_paren_term tail in
          let (term2, tail) = parse_paren_term tail in
          (App (term1, term2), tail)
      | Delim '$' ->
          let (name, tail) = parse_var tail in
          let (_, tail) = parse_token (Delim ':') tail in
          let (typ, tail) = parse_paren_term tail in
          let (_, tail) = parse_token (Delim '.') tail in
          let (body, tail) = parse_paren_term tail in
          (Lam (name, typ, body), tail)
      | Delim '?' ->
          let (name, tail) = parse_var tail in
          let (_, tail) = parse_token (Delim ':') tail in
          let (typ, tail) = parse_paren_term tail in
          let (_, tail) = parse_token (Delim '.') tail in
          let (body, tail) = parse_paren_term tail in
          (Type (name, typ, body), tail)
      | Delim _ -> raise (SyntaxError Empty)
      | Ident name when length name = 1 -> (Var name.[0], tail)
      | Ident name ->
          let (_, tail) = parse_token (Delim '[') tail in
          let (term_list, tail) =
            (match parse_token_if (Delim ']') tail with
            | Some ((_, tail)) -> ([], tail)
            | None ->
                let (term_list, tail) = parse_paren_term_list1 tail in
                let (_, tail) = parse_token (Delim ']') tail in
                (term_list, tail)
            ) in
          (Const (name, term_list), tail)
      )

and parse_paren_term_list1 rest =
  let (term, rest) = parse_paren_term rest in
  match parse_token_if (Delim ',') rest with
  | Some((_, rest)) ->
      let (term_list, rest) = parse_paren_term_list1 rest in
      (term :: term_list, rest)
  | None -> ([term], rest)

and parse_paren_term rest =
  let (_, rest) = parse_token (Delim '(') rest in
  let (term, rest) = parse_term rest in
  let (_, rest) = parse_token (Delim ')') rest in
  (term, rest)

