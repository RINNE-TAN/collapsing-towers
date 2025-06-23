
import CollapsingTowers.TwoLevelPCP.Progress
import CollapsingTowers.TwoLevelPCP.Preservation.Defs
@[simp]
def stuck (st₀ : Store) (e₀ : Expr) : Prop :=
  ¬(∃ st₁ e₁, step (st₀, e₀) (st₁, e₁)) ∧ ¬value e₀

theorem soundness :
  ∀ σ₀ st₀ st₁ e₀ e₁ τ φ,
    stepn (st₀, e₀) (st₁, e₁) →
    well_store σ₀ st₀ →
    typing_reification [] σ₀ e₀ τ φ →
    ¬stuck st₁ e₁ :=
  by
  intros σ₀ st₀ st₁ e₀ e₁ τ φ Hstepn HwellStore Hτ
  simp; intro HNorm
  have ⟨σ₁, φ₁, HwellStore₁, IHτ₁, HφLe₁⟩ := preservation_stepn _ _ _ _ _ _ _ Hstepn HwellStore Hτ
  cases progress _ _ _ _ _ HwellStore₁ IHτ₁ with
  | inl Hvalue => apply Hvalue
  | inr Hstep =>
    have ⟨_, _, Hstep⟩ := Hstep
    exfalso; apply HNorm; apply Hstep
