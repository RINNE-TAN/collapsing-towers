
import Mathlib.Data.Nat.Basic
inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)
  | rep (τ : Ty)

@[simp]
def wfty₁ : Ty -> Prop
  | .nat => true
  | .arrow τ𝕒 τ𝕓 => wfty₁ τ𝕒 /\ wfty₁ τ𝕓
  | .rep _ => false

mutual
  @[simp]
  def wfty₂ : Ty -> Prop
    | .nat => false
    | .arrow τ𝕒 τ𝕓 => (wfty₂ τ𝕒 /\ wfty τ𝕓) \/ (wfty τ𝕒 /\ wfty₂ τ𝕓)
    | .rep τ => wfty₁ τ
  @[simp]
  def wfty (τ : Ty) : Prop :=
    wfty₁ τ \/ wfty₂ τ
end

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam₁ (e : Expr)
  | lam₂ (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit₁ (n : ℕ)
  | lit₂ (n : ℕ)
  | plus₁ (l : Expr) (r : Expr)
  | plus₂ (l : Expr) (r : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | let𝕔 (b : Expr) (e : Expr)

abbrev TEnv :=
  List Ty

abbrev VEnv :=
  List Expr
