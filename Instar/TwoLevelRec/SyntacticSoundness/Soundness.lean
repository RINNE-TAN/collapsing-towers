import Instar.TwoLevelRec.SyntacticSoundness.Preservation
import Instar.TwoLevelRec.SyntacticSoundness.Progress

@[simp]
def stuck (e₀ : Expr) : Prop :=
  ¬(∃ e₁, e₀ ⭢ e₁) ∧ ¬value e₀

theorem soundness :
  ∀ e₀ e₁ τ ε,
    (e₀ ⭢* e₁) →
    typing_reification ⦰ e₀ τ ε →
    ¬stuck e₁ :=
  by
  intros e₀ e₁ τ ε Hstepn Hτ
  simp; intro HNorm
  have ⟨ε₁, IHτ₁, HεLe₁⟩ := preservation.stepn _ _ _ _ Hstepn Hτ
  match progress _ _ _ IHτ₁ with
  | .inl Hstep =>
    have ⟨_, Hstep⟩ := Hstep
    exfalso; apply HNorm _ Hstep
  | .inr Hvalue => apply Hvalue
