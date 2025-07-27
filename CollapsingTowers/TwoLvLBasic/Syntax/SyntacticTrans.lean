import CollapsingTowers.TwoLvLBasic.Syntax.Basic

@[simp]
def opening (i : ℕ) (v : Expr) : Expr → Expr
  | .bvar j => if j = i then v else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) v e)
  | .lift e => .lift (opening i v e)
  | .app₁ f arg => .app₁ (opening i v f) (opening i v arg)
  | .app₂ f arg => .app₂ (opening i v f) (opening i v arg)
  | .lit n => .lit n
  | .run e => .run (opening i v e)
  | .code e => .code (opening i v e)
  | .reflect e => .reflect (opening i v e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) v e)
  | .lets b e => .lets (opening i v b) (opening (i + 1) v e)
  | .lets𝕔 b e => .lets𝕔 (opening i v b) (opening (i + 1) v e)

notation:max "{" i " ↦ " x "}" e => opening i (Expr.fvar x) e

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr → Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam e => .lam (closing (i + 1) x e)
  | .lift e => .lift (closing i x e)
  | .app₁ f arg => .app₁ (closing i x f) (closing i x arg)
  | .app₂ f arg => .app₂ (closing i x f) (closing i x arg)
  | .lit n => .lit n
  | .run e => .run (closing i x e)
  | .code e => .code (closing i x e)
  | .reflect e => .reflect (closing i x e)
  | .lam𝕔 e => .lam𝕔 (closing (i + 1) x e)
  | .lets b e => .lets (closing i x b) (closing (i + 1) x e)
  | .lets𝕔 b e => .lets𝕔 (closing i x b) (closing (i + 1) x e)

notation:max "{" i " ↤ " x "}" e => closing i x e

@[simp]
def subst (x : ℕ) (v : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .lift e => .lift (subst x v e)
  | .app₁ f arg => .app₁ (subst x v f) (subst x v arg)
  | .app₂ f arg => .app₂ (subst x v f) (subst x v arg)
  | .lit n => .lit n
  | .run e => .run (subst x v e)
  | .code e => .code (subst x v e)
  | .reflect e => .reflect (subst x v e)
  | .lam𝕔 e => .lam𝕔 (subst x v e)
  | .lets b e => .lets (subst x v b) (subst x v e)
  | .lets𝕔 b e => .lets𝕔 (subst x v b) (subst x v e)

@[simp]
def maping𝕔 (i : ℕ) (e : Expr) : Expr :=
  match e with
  | .bvar j => if j == i then (.code (.bvar i)) else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (maping𝕔 (i + 1) e)
  | .lift e => .lift (maping𝕔 i e)
  | .app₁ f arg => .app₁ (maping𝕔 i f) (maping𝕔 i arg)
  | .app₂ f arg => .app₂ (maping𝕔 i f) (maping𝕔 i arg)
  | .lit n => .lit n
  | .run e => .run (maping𝕔 i e)
  | .code e => .code (maping𝕔 i e)
  | .reflect e => .reflect (maping𝕔 i e)
  | .lam𝕔 e => .lam𝕔 (maping𝕔 (i + 1) e)
  | .lets b e => .lets (maping𝕔 i b) (maping𝕔 (i + 1) e)
  | .lets𝕔 b e => .lets𝕔 (maping𝕔 i b) (maping𝕔 (i + 1) e)

@[simp]
def shiftl_at (x : ℕ) (n : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x ≤ y then .fvar (y + n) else .fvar y
  | .lam e => .lam (shiftl_at x n e)
  | .lift e => .lift (shiftl_at x n e)
  | .app₁ f arg => .app₁ (shiftl_at x n f) (shiftl_at x n arg)
  | .app₂ f arg => .app₂ (shiftl_at x n f) (shiftl_at x n arg)
  | .lit n => .lit n
  | .run e => .run (shiftl_at x n e)
  | .code e => .code (shiftl_at x n e)
  | .reflect e => .reflect (shiftl_at x n e)
  | .lam𝕔 e => .lam𝕔 (shiftl_at x n e)
  | .lets b e => .lets (shiftl_at x n b) (shiftl_at x n e)
  | .lets𝕔 b e => .lets𝕔 (shiftl_at x n b) (shiftl_at x n e)

@[simp]
def shiftr_at (x : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .lam e => .lam (shiftr_at x e)
  | .lift e => .lift (shiftr_at x e)
  | .app₁ f arg => .app₁ (shiftr_at x f) (shiftr_at x arg)
  | .app₂ f arg => .app₂ (shiftr_at x f) (shiftr_at x arg)
  | .lit n => .lit n
  | .run e => .run (shiftr_at x e)
  | .code e => .code (shiftr_at x e)
  | .reflect e => .reflect (shiftr_at x e)
  | .lam𝕔 e => .lam𝕔 (shiftr_at x e)
  | .lets b e => .lets (shiftr_at x b) (shiftr_at x e)
  | .lets𝕔 b e => .lets𝕔 (shiftr_at x b) (shiftr_at x e)
