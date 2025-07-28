import CollapsingTowers.TwoLvLBasic.Syntax.Lc
import CollapsingTowers.TwoLvLBasic.Syntax.Closed

@[simp]
def wf_at (e : Expr) (x : ℕ) : Prop := lc e ∧ closed_at e x

@[simp]
def wf (e : Expr) : Prop := wf_at e 0
