
import CollapsingTowers.TwoLevelPCP.Progress
import CollapsingTowers.TwoLevelPCP.Preservation
@[simp]
def stuck (st₀ : Store) (e₀ : Expr) : Prop :=
  ¬(∃ st₁ e₁, step (st₀, e₀) (st₁, e₁)) ∧ ¬value e₀

theorem stepn_preservation :
  ∀ σ₀ st₀ st₁ e₀ e₁ τ φ₀,
    stepn (st₀, e₀) (st₁, e₁) →
    well_store σ₀ st₀ →
    typing_reification [] σ₀ e₀ τ φ₀ →
    ∃ σ₁ φ₁,
      well_store (σ₁ ++ σ₀) st₁ ∧
      typing_reification [] (σ₁ ++ σ₀) e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro σ₀ st₀ st₁ e₀ e₁ τ φ₀ Hstepn HwellStore Hτ
  generalize HEq : (st₁, e₁) = E₁
  rw [HEq] at Hstepn
  induction Hstepn generalizing st₁ e₁ with
  | refl =>
    simp at HEq; rw [HEq.left, HEq.right]
    exists [], φ₀
  | multi E₁' E₂' _ Hstep IHτ =>
    have ⟨st₁', e₁'⟩ := E₁'
    have ⟨st₂', e₂'⟩ := E₂'
    simp at HEq; rw [HEq.left, HEq.right]
    have ⟨σ₁, φ₁, HwellStore₁, IHτ₁, HφLe₁⟩ := IHτ st₁' e₁' rfl
    have ⟨σ₂, φ₂, HwellStore₂, IHτ₂, HφLe₂⟩ := preservation _ _ _ _ _ _ _ Hstep HwellStore₁ IHτ₁
    exists (σ₂ ++ σ₁), φ₂
    rw [List.append_assoc]
    constructor; apply HwellStore₂
    constructor; apply IHτ₂
    apply le_trans; apply HφLe₂; apply HφLe₁

theorem soundness :
  ∀ σ₀ st₀ st₁ e₀ e₁ τ φ,
    stepn (st₀, e₀) (st₁, e₁) →
    well_store σ₀ st₀ →
    typing_reification [] σ₀ e₀ τ φ →
    ¬stuck st₁ e₁ :=
  by
  intros σ₀ st₀ st₁ e₀ e₁ τ φ Hstepn HwellStore Hτ
  simp; intro HNorm
  have ⟨σ₁, φ₁, HwellStore₁, IHτ₁, HφLe₁⟩ := stepn_preservation _ _ _ _ _ _ _ Hstepn HwellStore Hτ
  cases progress _ _ _ _ _ HwellStore₁ IHτ₁ with
  | inl Hvalue => apply Hvalue
  | inr Hstep =>
    have ⟨_, _, Hstep⟩ := Hstep
    exfalso; apply HNorm; apply Hstep
