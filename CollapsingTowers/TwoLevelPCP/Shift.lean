
import CollapsingTowers.TwoLevelPCP.Syntax
import CollapsingTowers.TwoLevelPCP.OpenClose
@[simp]
def shiftr_at (x : ℕ) : Expr -> Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .lam₁ e => .lam₁ (shiftr_at x e)
  | .lift e => .lift (shiftr_at x e)
  | .app₁ f arg => .app₁ (shiftr_at x f) (shiftr_at x arg)
  | .app₂ f arg => .app₂ (shiftr_at x f) (shiftr_at x arg)
  | .lit₁ n => .lit₁ n
  | .plus₁ l r => .plus₁ (shiftr_at x l) (shiftr_at x r)
  | .plus₂ l r => .plus₂ (shiftr_at x l) (shiftr_at x r)
  | .code e => .code (shiftr_at x e)
  | .reflect e => .reflect (shiftr_at x e)
  | .lam𝕔 e => .lam𝕔 (shiftr_at x e)
  | .lets b e => .lets (shiftr_at x b) (shiftr_at x e)
  | .let𝕔 b e => .let𝕔 (shiftr_at x b) (shiftr_at x e)
