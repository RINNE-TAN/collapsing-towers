
import CollapsingTowers.TwoLevelBasic.SemEquiv.Preservation
import CollapsingTowers.TwoLevelBasic.SemEquiv.CtxEquiv
-- e₀ ↦* e₁
-- ∅ ⊢ e₀ : τ
-- ————————————————————————
-- ∅ ⊢ ‖e₀‖ ≈𝑐𝑡𝑥 ‖e₁‖ : ‖τ‖
theorem ctx_equiv_preservation :
  ∀ e₀ e₁ τ φ,
    stepn e₀ e₁ →
    typing_reification [] e₀ τ φ →
    ctx_equiv [] ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros e₀ e₁ τ φ Hstepn Hτ
  apply sem_soundness
  apply sem_reification_preservation_stepn
  apply Hstepn; apply Hτ

-- e₀ ↦* v
-- ∅ ⊢ e₀ : <τ>
-- ————————————————————
-- v = code e₁
-- ∅ ⊢ ‖e₀‖ ≈𝑐𝑡𝑥 e₁ : τ
theorem ctx_equiv_preservation_rep :
  ∀ e₀ v τ φ,
    stepn e₀ v →
    value v →
    typing_reification [] e₀ (.rep τ) φ →
    ∃ e₁,
      v = .code e₁ ∧
      ctx_equiv [] ‖e₀‖ e₁ τ :=
  by
  intros e₀ v τ φ Hstepn Hvalue Hτr₀
  have ⟨_, Hτr₁, _⟩ := preservation_stepn _ _ _ _ Hstepn Hτr₀
  have ⟨e₁, HEq, Hτe₁⟩ := typing_rep_value _ _ _ Hvalue Hτr₁
  rw [HEq] at Hstepn
  exists e₁
  constructor; apply HEq
  rw [← typing_dyn_erase_id _ _ _ _ Hτe₁, ← typing_dyn_erase_ty_id _ _ _ _ Hτe₁]
  apply ctx_equiv_preservation _ _ _ _ Hstepn Hτr₀
