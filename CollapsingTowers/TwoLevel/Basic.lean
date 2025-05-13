
import Mathlib.Data.Nat.Basic
inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)
  | rep (τ : Ty)

@[simp]
def wf₁ : Ty -> Prop
  | .nat => true
  | .arrow τ𝕒 τ𝕓 => wf₁ τ𝕒 /\ wf₁ τ𝕓
  | .rep _ => false

@[simp]
def wf₂ : Ty -> Prop
  | .nat => false
  | .arrow τ𝕒 τ𝕓 => wf₂ τ𝕒 \/ wf₂ τ𝕓
  | .rep τ => wf₁ τ

@[simp]
def wf (τ : Ty) : Prop :=
  wf₁ τ \/ wf₂ τ

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
