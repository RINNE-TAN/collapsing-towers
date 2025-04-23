
import Mathlib.Data.Finset.Basic
inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam (e : Expr)
  | app (f : Expr) (arg : Expr)
  | unit

inductive Ty : Type where
  | ty_unit
  | ty_fun : Ty -> Ty -> Ty

@[simp]
def fv : Expr → Finset ℕ
  | .bvar _ => ∅
  | .fvar y => { y }
  | .lam e => fv e
  | .app f arg => fv f ∪ fv arg
  | .unit => ∅
