import Mathlib.Data.Nat.Basic

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit (n : ℕ)
  | lift (e : Expr)
  | run (e : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | lets𝕔 (b : Expr) (e : Expr)
  | unit
  | loc (l : ℕ)
  | alloc₁ (e : Expr)
  | load₁ (e : Expr)
  | store₁ (l : Expr) (r : Expr)
  | alloc₂ (e : Expr)
  | load₂ (e : Expr)
  | store₂ (l : Expr) (r : Expr)
