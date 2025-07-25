import CollapsingTowers.TwoLvLBasic.Syntax.Basic

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar j => j < i
  | .fvar _ => true
  | .lam e => lc_at e (i + 1)
  | .lift e => lc_at e i
  | .app₁ f arg => lc_at f i ∧ lc_at arg i
  | .app₂ f arg => lc_at f i ∧ lc_at arg i
  | .lit _ => true
  | .run e => lc_at e i
  | .code e => lc_at e i
  | .reflect e => lc_at e i
  | .lam𝕔 e => lc_at e (i + 1)
  | .lets b e => lc_at b i ∧ lc_at e (i + 1)
  | .lets𝕔 b e => lc_at b i ∧ lc_at e (i + 1)

@[simp]
def lc e := lc_at e 0
