
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelBasic.Effect
inductive Stage : Type where
  | stat
  | dyn

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effects)
  | fragment (τ : Ty)
  | rep (τ : Ty)

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
  | let𝕔 (b : Expr) (e : Expr)
