import CollapsingTowers.TwoLevelBasic.SyntacticSoundness.Preservation
import CollapsingTowers.TwoLevelBasic.SyntacticSoundness.Progress

@[simp]
def stuck (e₀ : Expr) : Prop :=
  ¬(∃ e₁, e₀ ⇝ e₁) ∧ ¬value e₀

theorem soundness :
  ∀ e₀ e₁ τ φ,
    (e₀ ⇝* e₁) →
    typing_reification ⦰ e₀ τ φ →
    ¬stuck e₁ :=
  by
  intros e₀ e₁ τ φ Hstepn Hτ
  simp; intro HNorm
  have ⟨φ₁, IHτ₁, HφLe₁⟩ := preservation.stepn _ _ _ _ Hstepn Hτ
  match progress _ _ _ IHτ₁ with
  | .inl Hstep =>
    have ⟨_, Hstep⟩ := Hstep
    exfalso; apply HNorm _ Hstep
  | .inr Hvalue => apply Hvalue
