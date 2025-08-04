import CollapsingTowers.TwoLevelRec.SyntacticTyping.Preservation
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Progress

@[simp]
def stuck (e₀ : Expr) : Prop :=
  ¬(∃ e₁, e₀ ⇝ e₁) ∧ ¬value e₀

theorem soundness :
  ∀ e₀ e₁ τ φ,
    (e₀ ⇝* e₁) →
    typing_reification [] e₀ τ φ →
    ¬stuck e₁ :=
  by
  intros e₀ e₁ τ φ Hstepn Hτ
  simp; intro HNorm
  have ⟨φ₁, IHτ₁, HφLe₁⟩ := preservation.stepn _ _ _ _ Hstepn Hτ
  cases progress _ _ _ IHτ₁ with
  | inl Hvalue => apply Hvalue
  | inr Hstep =>
    have ⟨_, Hstep⟩ := Hstep
    exfalso; apply HNorm; apply Hstep
