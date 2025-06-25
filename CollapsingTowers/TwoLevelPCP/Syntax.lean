
import Mathlib.Data.Nat.Basic
import CollapsingTowers.TwoLevelPCP.Effect
inductive Stage : Type where
  | stat
  | dyn

inductive BinOp : Type where
  | add
  | mul

@[simp]
def eval : BinOp → ℕ → ℕ → ℕ
  | .add => Nat.add
  | .mul => Nat.mul

inductive Ty : Type where
  | nat
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effects)
  | fragment (τ : Ty)
  | rep (τ : Ty)
  | ref (τ : Ty)

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam₁ (e : Expr)
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit₁ (n : ℕ)
  | binary₁ (op : BinOp) (l : Expr) (r : Expr)
  | binary₂ (op : BinOp) (l : Expr) (r : Expr)
  | lift (e : Expr)
  | run (e : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | let𝕔 (b : Expr) (e : Expr)
  | loc (l : ℕ)
  | load₁ (e : Expr)
  | alloc₁ (e : Expr)
  | store₁ (l : Expr) (r : Expr)
  | load₂ (e : Expr)
  | alloc₂ (e : Expr)
  | store₂ (l : Expr) (r : Expr)
  | ifz₁ (c : Expr) (l : Expr) (r : Expr)
  | ifz₂ (c : Expr) (l : Expr) (r : Expr)
  | fix₁ (e : Expr)
