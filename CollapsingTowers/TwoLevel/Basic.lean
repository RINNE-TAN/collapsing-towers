
import Mathlib.Data.Nat.Basic
inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty)
  | rep (τ : Ty)

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam₁ (e : Expr)
  | lam₂ (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit₁ (n : ℕ)
  | lit₂ (n : Expr)
  | plus₁ (l : Expr) (r : Expr)
  | plus₂ (l : Expr) (r : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | let𝕔 (b : Expr) (e : Expr)

@[simp]
def user_def : Expr -> Prop
  | .bvar _ => true
  | .lam₁ e => user_def e
  | .lam₂ e => user_def e
  | .app₁ f arg => user_def f ∧ user_def arg
  | .app₂ f arg => user_def f ∧ user_def arg
  | .lit₁ _ => true
  | .lit₂ n => user_def n
  | .plus₁ l r => user_def l ∧ user_def r
  | .plus₂ l r => user_def l ∧ user_def r
  | .lets b e => user_def b ∧ user_def e
  | .fvar _ => false
  | .code _ => false
  | .reflect _ => false
  | .lam𝕔 _ => false
  | .let𝕔 _ _ => false

abbrev TEnv :=
  List Ty

abbrev VEnv :=
  List Expr
