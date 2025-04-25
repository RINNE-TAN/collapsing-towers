
import CollapsingTowers.TwoLevel.Basic
import Mathlib.Data.Finset.Basic
@[simp]
def fv : Expr → Finset ℕ
  | .bvar _ => ∅
  | .fvar y => { y }
  | .lam₁ e => fv e
  | .lam₂ e => fv e
  | .app₁ f arg => fv f ∪ fv arg
  | .app₂ f arg => fv f ∪ fv arg
  | .lit₁ _ => ∅
  | .lit₂ _ => ∅
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .let𝕔 b e => fv b ∪ fv e

@[simp]
def subst (x : ℕ) (v : Expr) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x == y then v else .fvar y
  | .lam₁ e => .lam₁ (subst x v e)
  | .lam₂ e => .lam₂ (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)

@[simp]
def opening (i : ℕ) (v : Expr) : Expr -> Expr
  | .bvar j => if j == i then v else .bvar i
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (opening (i + 1) v e)
  | .lam₂ e => .lam₂ (opening (i + 1) v e)
  | .app₁ f arg => .app₁ (opening i v f) (opening i v arg)
  | .app₂ f arg => .app₂ (opening i v f) (opening i v arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .code e => .code (opening i v e)
  | .reflect e => .reflect (opening i v e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) v e)
  | .let𝕔 b e => .let𝕔 (opening i v b) (opening (i + 1) v e)

@[simp]
def open₀ (v : Expr) : Expr -> Expr :=
  opening 0 v

inductive lc : Expr -> Prop where
  | fvar : ∀ x, lc (.fvar x)
  | lam₁ : ∀ x e, lc (open₀ (.fvar x) e) -> lc (.lam₁ e)
  | lam₂ : ∀ x e, lc (open₀ (.fvar x) e) -> lc (.lam₂ e)
  | app₁ : ∀ f arg, lc f -> lc arg -> lc (.app₁ f arg)
  | app₂ : ∀ f arg, lc f -> lc arg -> lc (.app₂ f arg)
  | lit₁ : ∀ n, lc (.lit₁ n)
  | lit₂ : ∀ n, lc (.lit₂ n)
  | code : ∀ e, lc e -> lc (.code e)
  | reflect : ∀ e, lc e -> lc (.reflect e)
  | lam𝕔 : ∀ x e, lc (open₀ (.fvar x) e) -> lc (.lam𝕔 e)
  | let𝕔 : ∀ x b e, lc b -> lc (open₀ (.fvar x) e) -> lc (.let𝕔 b e)

inductive value : Expr -> Prop where
  | lam : ∀ e, lc (.lam₁ e) -> value (.lam₁ e)
  | lit : ∀ n, value (.lit₁ n)
  | code : ∀ e, lc e -> value (.code e)
