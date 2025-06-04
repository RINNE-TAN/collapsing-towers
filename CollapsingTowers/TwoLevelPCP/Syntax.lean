
import Mathlib.Data.Nat.Basic
inductive Stage : Type where
  | stat
  | dyn

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)
  | fragment (τ : Ty)
  | rep (τ : Ty)

def well_binding_time : Stage → Ty → Prop
  | .stat, .nat => true
  | .stat, (.arrow _ _) => true
  | .stat, (.fragment _) => true
  | .stat, _ => false
  | .dyn, .nat => true
  | .dyn, (.arrow _ _) => true
  | .dyn, _ => false

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam₁ (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit₁ (n : ℕ)
  | plus₁ (l : Expr) (r : Expr)
  | plus₂ (l : Expr) (r : Expr)
  | lift (e : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | let𝕔 (b : Expr) (e : Expr)
