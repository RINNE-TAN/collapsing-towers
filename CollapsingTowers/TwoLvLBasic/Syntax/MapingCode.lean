import CollapsingTowers.TwoLvLBasic.Syntax.Basic

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
