
import CollapsingTowers.TwoLevel.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
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
  | .plus₁ l r => fv l ∪ fv r
  | .plus₂ l r => fv l ∪ fv r
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .lets b e => fv b ∪ fv e
  | .let𝕔 b e => fv b ∪ fv e

@[simp]
def fresh (e : Expr) : ℕ :=
  (fv e).max.elim 0 .succ

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
  | .plus₁ l r => .plus₁ (subst x v l) (subst x v r)
  | .plus₂ l r => .plus₂ (subst x v l) (subst x v r)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)

@[simp]
def opening (i : ℕ) (x : Expr) : Expr -> Expr
  | .bvar j => if j == i then x else .bvar i
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (opening (i + 1) x e)
  | .lam₂ e => .lam₂ (opening (i + 1) x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (opening i x l) (opening i x r)
  | .plus₂ l r => .plus₂ (opening i x l) (opening i x r)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)

@[simp]
def open₀ (i: ℕ): Expr -> Expr := opening 0 (.fvar i)

@[simp]
def openSubst (tgt: Expr) (within: Expr) := opening 0 tgt within

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr -> Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam₁ e => .lam₁ (closing (i + 1) x e)
  | .lam₂ e => .lam₂ (closing (i + 1) x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (closing i x l) (closing i x r)
  | .plus₂ l r => .plus₂ (closing i x l) (closing i x r)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (closing i x b) (closing (i + 1) x e)

@[simp]
def close₀ : ℕ -> Expr -> Expr := closing 0

inductive lc : Expr -> Prop where
  | fvar : ∀ x, lc (.fvar x)
  | lam₁ : ∀ e x, lc (open₀ x e) -> lc (.lam₁ e)
  | lam₂ : ∀ e x, lc (open₀ x e) -> lc (.lam₂ e)
  | app₁ : ∀ f arg, lc f -> lc arg -> lc (.app₁ f arg)
  | app₂ : ∀ f arg, lc f -> lc arg -> lc (.app₂ f arg)
  | lit₁ : ∀ n, lc (.lit₁ n)
  | lit₂ : ∀ n, lc (.lit₂ n)
  | plus₁ : ∀ l r, lc l -> lc r -> lc (.plus₁ l r)
  | plus₂ : ∀ l r, lc l -> lc r -> lc (.plus₂ l r)
  | code : ∀ e, lc e -> lc (.code e)
  | reflect : ∀ e, lc e -> lc (.reflect e)
  | lam𝕔 : ∀ e x, lc (open₀ x e) -> lc (.lam𝕔 e)
  | lets : ∀ b e x, lc b -> lc (open₀ x e) -> lc (.lets b e)
  | let𝕔 : ∀ b e x, lc b -> lc (open₀ x e) -> lc (.let𝕔 b e)

@[simp]
def closeCode (e: Expr) (i: ℕ) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (closeCode e (i + 1))
  | .lam₂ e => .lam₂ (closeCode e (i + 1))
  | .app₁ f arg => .app₁ (closeCode f i) (closeCode arg i)
  | .app₂ f arg => .app₂ (closeCode f i) (closeCode arg i)
  | .lit₁ n => .lit₁ n
  | .lit₂ n => .lit₂ n
  | .plus₁ l r => .plus₁ (closeCode l i) (closeCode r i)
  | .plus₂ l r => .plus₂ (closeCode l i) (closeCode r i)
  | .code e => .code (closeCode e i)
  | .reflect e => .reflect (closeCode e i)
  | .lam𝕔 e => .lam𝕔 (closeCode e (i + 1))
  | .lets b e => .lets (closeCode b i) (closeCode e (i + 1))
  | .let𝕔 b e => .let𝕔 (closeCode b i) (closeCode e (i + 1))

example :
  closeCode (.app₁ (.bvar 0) (.lam₁ (.bvar 1))) 0 =
  (.app₁ (.code (.bvar 0)) (.lam₁ (.code (.bvar 1)))) := by simp

inductive value : Expr -> Prop where
  | lam : ∀ e, lc (.lam₁ e) -> value (.lam₁ e)
  | lit : ∀ n, value (.lit₁ n)
  | code : ∀ e, lc e -> value (.code e)
