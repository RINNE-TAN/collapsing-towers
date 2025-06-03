
import CollapsingTowers.TwoLevelPCP.Syntax

-- Definitions
@[simp]
def subst (x : ℕ) (v : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam₁ e => .lam₁ (subst x v e)
  | .lift e => .lift (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit₁ n => .lit₁ n
  | .plus₁ l r => .plus₁ (subst x v l) (subst x v r)
  | .plus₂ l r => .plus₂ (subst x v l) (subst x v r)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .let𝕔 b e => .let𝕔 (subst x v b) (subst x v e)

-- opening i t1 t2 = [i → t1]t2
@[simp]
def opening (i : ℕ) (x : Expr) : Expr → Expr
  | .bvar j => if j = i then x else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (opening (i + 1) x e)
  | .lift e => .lift (opening i x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit₁ n => .lit₁ n
  | .plus₁ l r => .plus₁ (opening i x l) (opening i x r)
  | .plus₂ l r => .plus₂ (opening i x l) (opening i x r)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (opening i x b) (opening (i + 1) x e)

@[simp]
def open₀ (x : ℕ) : Expr → Expr :=
  opening 0 (.fvar x)

@[simp]
def open_subst (tgt : Expr) (within : Expr) :=
  opening 0 tgt within

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr → Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam₁ e => .lam₁ (closing (i + 1) x e)
  | .lift e => .lift (closing i x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit₁ n => .lit₁ n
  | .plus₁ l r => .plus₁ (closing i x l) (closing i x r)
  | .plus₂ l r => .plus₂ (closing i x l) (closing i x r)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .let𝕔 b e => .let𝕔 (closing i x b) (closing (i + 1) x e)

@[simp]
def close₀ : ℕ → Expr → Expr :=
  closing 0

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (f : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar x => x < f
  | .lam₁ e => closed_at e f
  | .lift e => closed_at e f
  | .app₁ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .app₂ e1 e2 => closed_at e1 f ∧ closed_at e2 f
  | .lit₁ _ => true
  | .plus₁ l r => closed_at l f ∧ closed_at r f
  | .plus₂ l r => closed_at l f ∧ closed_at r f
  | .code e => closed_at e f
  | .reflect e => closed_at e f
  | .lam𝕔 e => closed_at e f
  | .lets b e => closed_at b f ∧ closed_at e f
  | .let𝕔 b e => closed_at b f ∧ closed_at e f

-- closedness condition for bound variables
@[simp]
def closedb_at (e : Expr) (b : ℕ) : Prop :=
  match e with
  | .bvar x => x < b
  | .fvar _ => true
  | .lam₁ e => closedb_at e (b + 1)
  | .lift e => closedb_at e b
  | .app₁ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .app₂ e1 e2 => closedb_at e1 b ∧ closedb_at e2 b
  | .lit₁ _ => true
  | .plus₁ l r => closedb_at l b ∧ closedb_at r b
  | .plus₂ l r => closedb_at l b ∧ closedb_at r b
  | .code e => closedb_at e b
  | .reflect e => closedb_at e b
  | .lam𝕔 e => closedb_at e (b + 1)
  | .lets e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)
  | .let𝕔 e1 e2 => closedb_at e1 b ∧ closedb_at e2 (b + 1)

@[simp]
def lc e :=
  closedb_at e 0

@[simp]
def maping𝕔 (e : Expr) (i : ℕ) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam₁ e => .lam₁ (maping𝕔 e (i + 1))
  | .lift e => .lift (maping𝕔 e i)
  | .app₁ f arg => .app₁ (maping𝕔 f i) (maping𝕔 arg i)
  | .app₂ f arg => .app₂ (maping𝕔 f i) (maping𝕔 arg i)
  | .lit₁ n => .lit₁ n
  | .plus₁ l r => .plus₁ (maping𝕔 l i) (maping𝕔 r i)
  | .plus₂ l r => .plus₂ (maping𝕔 l i) (maping𝕔 r i)
  | .code e => .code (maping𝕔 e i)
  | .reflect e => .reflect (maping𝕔 e i)
  | .lam𝕔 e => .lam𝕔 (maping𝕔 e (i + 1))
  | .lets b e => .lets (maping𝕔 b i) (maping𝕔 e (i + 1))
  | .let𝕔 b e => .let𝕔 (maping𝕔 b i) (maping𝕔 e (i + 1))

@[simp]
def map𝕔₀ (e : Expr) : Expr :=
  maping𝕔 e 0
