import Mathlib.Data.Nat.Basic

inductive Effect : Type where
  | pure
  | reify

notation:max "∅" => Effect.pure

@[simp]
def Effect.union : Effect → Effect → Effect
  | .pure, .pure => .pure
  | .reify, _ => .reify
  | _, .reify => .reify

@[simp]
instance : Union Effect where union := Effect.union

inductive Stage : Type where
  | stat
  | dyn

notation:max "𝟙" => Stage.stat

notation:max "𝟚" => Stage.dyn

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effect)
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
  | lets𝕔 (b : Expr) (e : Expr)
