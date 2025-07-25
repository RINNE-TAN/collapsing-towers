import CollapsingTowers.TwoLvLBasic.Syntax.Basic

@[simp]
def opening (i : ℕ) (x : Expr) : Expr → Expr
  | .bvar j => if j = i then x else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) x e)
  | .lift e => .lift (opening i x e)
  | .app₁ f arg => .app₁ (opening i x f) (opening i x arg)
  | .app₂ f arg => .app₂ (opening i x f) (opening i x arg)
  | .lit n => .lit n
  | .run e => .run (opening i x e)
  | .code e => .code (opening i x e)
  | .reflect e => .reflect (opening i x e)
  | .lam𝕔 e => .lam𝕔 (opening (i + 1) x e)
  | .lets b e => .lets (opening i x b) (opening (i + 1) x e)
  | .lets𝕔 b e => .lets𝕔 (opening i x b) (opening (i + 1) x e)

notation:max "{" i "↦" e₀ "}" e₁ => opening i e₀ e₁

notation:max "{" x "}" e => opening 0 (Expr.fvar x) e
