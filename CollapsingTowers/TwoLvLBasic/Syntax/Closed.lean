import CollapsingTowers.TwoLvLBasic.Syntax.Basic

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar y => y < x
  | .lam e => closed_at e x
  | .lift e => closed_at e x
  | .app₁ f arg => closed_at f x ∧ closed_at arg x
  | .app₂ f arg => closed_at f x ∧ closed_at arg x
  | .lit _ => true
  | .run e => closed_at e x
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .lam𝕔 e => closed_at e x
  | .lets b e => closed_at b x ∧ closed_at e x
  | .lets𝕔 b e => closed_at b x ∧ closed_at e x

@[simp]
def closed e := closed_at e 0
