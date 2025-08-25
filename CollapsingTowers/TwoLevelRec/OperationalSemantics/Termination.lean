import CollapsingTowers.TwoLevelRec.OperationalSemantics.Refine

-- e₁⇓ ≜ ∃ v, e ⇝* v
@[simp]
def termination (e : Expr) : Prop :=
  ∃ v, value v ∧ e ⇝* v
