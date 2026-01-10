open Type

open Format

let print_deriv_error book deriv err =
  printf "Derivation Error: ";
  (match err with
  | NotSort term ->
      printf "'%a' must be sort ('*' or '□')\n" pp_term term
  | NotSameName (x1, x2) ->
      printf "two variables '%s' and '%s' must be same\n" x1 x2
  | NotAlphaEquivalence (t1, t2) ->
      printf "two terms '%a' and '%a' must be α-equivalent\n" pp_term t1 pp_term t2
  | NotAlphaBetaDeltaEquiv (defs, t1, t2) ->
      printf "two terms '%a' and '%a' must be αβδ-equivalent in %a\n" pp_term t1 pp_term t2 pp_defs defs
  | EmptyContext ->
      printf "the context must be non-empty\n"
  | NotSameLengthContext (ctx1, ctx2) ->
      printf "the context length do not match\n";
      printf "'%a'\n" pp_ctx ctx1;
      printf "'%a'\n" pp_ctx ctx2
  | NotSameLengthDefinitions (defs1, defs2) ->
      printf "the definitions length do not match\n";
      printf "'%a'\n" pp_defs defs1;
      printf "'%a'\n" pp_defs defs2
  | NotSameLengthParamArg (name, ctx, args) ->
      printf "the cotnext of constant '%s' is '%a', but given argument list is '%a'" name pp_ctx ctx pp_term_list args
  | ConstAlreadyDefined (def, name) ->
      printf "constant '%s' is already defined:\n" name;
      printf "  %a\n" pp_def def
  | DoNotMatchDefinition (def1, def2) ->
      printf "'%a' and '%a' must match\n" pp_def def1 pp_def def2
  | UndefinedConst name ->
      printf "constant '%s' is undefined\n" name
  | NotTypeKind (typ, kind) ->
      printf "(%a, %a) must be (*, □)\n" pp_term typ pp_term kind
  | NotPi term ->
      printf "'%a' must be Π-term\n" pp_term term);
  print_deriv book deriv
