import CollapsingTowers.TwoLevelRec.Syntax.SyntacticTrans

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar y => y < x
  | .fix e => closed_at e x
  | .lift e => closed_at e x
  | .app₁ f arg => closed_at f x ∧ closed_at arg x
  | .app₂ f arg => closed_at f x ∧ closed_at arg x
  | .lit _ => true
  | .run e => closed_at e x
  | .code e => closed_at e x
  | .reflect e => closed_at e x
  | .fix𝕔 e => closed_at e x
  | .lets b e => closed_at b x ∧ closed_at e x
  | .lets𝕔 b e => closed_at b x ∧ closed_at e x

@[simp]
def closed e := closed_at e 0

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar j => j < i
  | .fvar _ => true
  | .fix e => lc_at e (i + 2)
  | .lift e => lc_at e i
  | .app₁ f arg => lc_at f i ∧ lc_at arg i
  | .app₂ f arg => lc_at f i ∧ lc_at arg i
  | .lit _ => true
  | .run e => lc_at e i
  | .code e => lc_at e i
  | .reflect e => lc_at e i
  | .fix𝕔 e => lc_at e (i + 2)
  | .lets b e => lc_at b i ∧ lc_at e (i + 1)
  | .lets𝕔 b e => lc_at b i ∧ lc_at e (i + 1)

@[simp]
def lc e := lc_at e 0
