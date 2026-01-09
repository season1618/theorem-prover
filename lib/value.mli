open Type

val normalize_by_eval : definitions -> term -> term
val alpha_beta_delta_equiv : definitions -> term -> term -> bool
