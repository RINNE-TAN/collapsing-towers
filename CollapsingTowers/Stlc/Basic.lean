
import Mathlib.Data.Finset.Basic
inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam (e : Expr)
  | app (f : Expr) (arg : Expr)
  | unit

inductive value : Expr -> Prop where
  | value_lam : value (.lam e)
  | value_unit : value .unit

@[simp]
def fv : Expr → Finset ℕ
  | .bvar _ => ∅
  | .fvar y => { y }
  | .lam e => fv e
  | .app f arg => fv f ∪ fv arg
  | .unit => ∅
