import CollapsingTowers.TwoLevelMut.SyntacticSoundness.Preservation
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.Progress

@[simp]
def stuck (σ₀ : Store) (e₀ : Expr) : Prop :=
  ¬(∃ σ₁ e₁, (⟨σ₀, e₀⟩ ⇝ ⟨σ₁, e₁⟩)) ∧ ¬value e₀

theorem soundness :
  ∀ σ₀ σ₁ e₀ e₁ τ φ,
    typing_reification ⦰ e₀ τ φ →
    (⟨σ₀, e₀⟩ ⇝* ⟨σ₁, e₁⟩) →
    ¬stuck σ₁ e₁ :=
  by
  intros σ₀ σ₁ e₀ e₁ τ φ₀ Hτ₀ Hstepn
  simp; intro HNorm
  have ⟨φ₁, Hτ₁, HφLe₁⟩ := preservation.stepn _ _ _ _ _ _ Hstepn Hτ₀
  match progress σ₁ _ _ _ Hτ₁ with
  | .inl Hstep =>
    have ⟨_, _, Hstep⟩ := Hstep
    exfalso; apply HNorm _ _ Hstep
  | .inr Hvalue => apply Hvalue
