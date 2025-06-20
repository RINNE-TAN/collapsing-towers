
import CollapsingTowers.TwoLevelPCP.Progress
import CollapsingTowers.TwoLevelPCP.Preservation
@[simp]
def stuck (e₀ : Expr) : Prop :=
  ¬(∃ e₁, step e₀ e₁) ∧ ¬value e₀

theorem stepn_preservation :
  ∀ σ e₀ e₁ τ φ₀,
    stepn e₀ e₁ →
    typing_reification [] σ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification [] σ e₁ τ φ₁ ∧ φ₁ ≤ φ₀ :=
  by
  intro σ e₀ e₁ τ φ₀ Hstepn Hτ
  induction Hstepn with
  | refl => exists φ₀
  | multi _ _ _ Hstep IHτ =>
    have ⟨φ₁, IHτ₁, HφLe₁⟩ := IHτ
    have ⟨φ₂, IHτ₂, HφLe₂⟩ := preservation _ _ _ _ _ Hstep IHτ₁
    exists φ₂; constructor
    apply IHτ₂; apply le_trans; apply HφLe₂; apply HφLe₁

theorem soundness :
  ∀ σ e₀ e₁ τ φ,
    stepn e₀ e₁ →
    typing_reification [] σ e₀ τ φ →
    ¬stuck e₁ :=
  by
  intros σ e₀ e₁ τ φ Hstepn Hτ
  simp; intro HNorm
  have ⟨φ₁, IHτ₁, HφLe₁⟩ := stepn_preservation _ _ _ _ _ Hstepn Hτ
  cases progress _ _ _ _ IHτ₁ with
  | inl Hvalue => apply Hvalue
  | inr Hstep =>
    have ⟨_, Hstep⟩ := Hstep
    exfalso; apply HNorm; apply Hstep
