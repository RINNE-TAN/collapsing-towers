
import CollapsingTowers.TwoLevel.Progresss
import CollapsingTowers.TwoLevel.Preservation
@[simp]
def stuck (e₀ : Expr) : Prop :=
  ¬(∃ e₁, step e₀ e₁) /\ ¬value e₀

theorem stepn_preservation : ∀ e₀ e₁ τ, stepn e₀ e₁ -> typing [] e₀ τ -> typing [] e₁ τ :=
  by
  intro e₀ e₁ τ Hstepn Hτ
  induction Hstepn with
  | refl => apply Hτ
  | multi _ _ _ Hstep IHτ =>
    apply preservation
    apply Hstep
    apply IHτ

theorem soundness : ∀ e₀ e₁ τ, stepn e₀ e₁ -> typing [] e₀ τ -> ¬stuck e₁ :=
  by
  intros e₀ e₁ τ Hstepn Hτ
  simp; intro HNorm
  cases progress _ _ (stepn_preservation _ _ _ Hstepn Hτ) with
  | inl HV => apply HV
  | inr Hstep =>
    obtain ⟨e₂, Hstep⟩ := Hstep
    exfalso; apply HNorm; apply Hstep
