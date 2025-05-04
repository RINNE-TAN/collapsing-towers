
import Mathlib.Data.Nat.Basic
inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)
  | rep (τ : Ty)

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam₁ (τ : Ty) (e : Expr)
  | lam₂ (τ : Ty) (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit₁ (n : ℕ)
  | lit₂ (n : ℕ)
  | plus₁ (l : Expr) (r : Expr)
  | plus₂ (l : Expr) (r : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (τ : Ty) (e : Expr)
  | lets (b : Expr) (e : Expr)
  | let𝕔 (b : Expr) (e : Expr)

abbrev TEnv :=
  List Ty

abbrev VEnv :=
  List Expr
