import CollapsingTowers.TwoLvLBasic.Syntax.Basic

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
