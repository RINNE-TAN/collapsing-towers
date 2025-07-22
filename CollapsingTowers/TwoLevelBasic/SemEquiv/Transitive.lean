import CollapsingTowers.TwoLevelBasic.SemEquiv.SemTyping
-- Γ ⊧ e₀ ≈ e₁ : τ
-- Γ ⊧ e₁ ≈ e₂ : τ
-- ———————————————
-- Γ ⊧ e₀ ≈ e₂ : τ
theorem sem_equiv_typing_trans :
  ∀ Γ e₀ e₁ e₂ τ,
    sem_equiv_typing Γ e₀ e₁ τ →
    sem_equiv_typing Γ e₁ e₂ τ →
    sem_equiv_typing Γ e₀ e₂ τ :=
  by admit
