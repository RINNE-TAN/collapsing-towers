
import Mathlib.Data.Nat.Basic
inductive Stage : Type where
  | fst
  | snd

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)
  | rep₁ (τ : Ty)
  | rep₂ (τ : Ty)

def binding_time : Stage → Ty → Prop
  | .fst, .nat => true
  | .fst, (.arrow _ _) => true
  | .fst, (.rep₁ _) => true
  | .fst, _ => false
  | .snd, .nat => true
  | .snd, (.arrow _ _) => true
  | .snd, _ => false

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
