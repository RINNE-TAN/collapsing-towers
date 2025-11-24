import CollapsingTowers.TwoLevelFinal.OperationalSemantics.Refine

-- e₁⇓ ≜ ∃ v σ, ⟨ϵ, e⟩ ⇝* ⟨σ, v⟩
@[simp]
def termination (e : Expr) : Prop :=
  ∃ v σ, value v ∧ ⟨ϵ, e⟩ ⇝* ⟨σ, v⟩
