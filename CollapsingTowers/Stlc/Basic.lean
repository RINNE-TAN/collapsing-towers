
inductive Expr : Type where
  | bvar (i : Nat)
  | fvar (x : String)
  | lam (e : Expr)
  | app (f : Expr) (arg : Expr)
  | unit

inductive value : Expr -> Prop where
  | value_lam : value (.lam e)
  | value_unit : value .unit
