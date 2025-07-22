
import CollapsingTowers.TwoLevelBasic.SemEquiv.Preservation
import CollapsingTowers.TwoLevelBasic.SemEquiv.ObsEquiv
theorem obs_stepn :
  ∀ e₀ e₁ τ φ,
    stepn e₀ e₁ →
    typing_reification [] e₀ τ φ →
    (Hτ₀ : typing ‖[]‖𝛾 Stage.stat ‖e₀‖ ‖τ‖𝜏 ∅) →
    (Hτ₁ : typing ‖[]‖𝛾 Stage.stat ‖e₁‖ ‖τ‖𝜏 ∅) →
    obs_equiv ⟨‖e₀‖, Hτ₀⟩ ⟨‖e₁‖, Hτ₁⟩ :=
  by
  intros e₀ e₁ τ φ Hstepn Hτr₀ Hτ₀ Hτ₁
  induction Hstepn
  case refl =>
    apply sem_soundness
    apply fundamental []
    apply Hτ₀
  case multi e₁ e₂ Hstepn Hstep IH =>
    have ⟨_, Hτr₀, _⟩ := preservation_stepn _ _ _ _ Hstepn Hτr₀
    apply obs_equiv_trans
    apply IH; rw [erase_typing_reification_iff_typing]
    apply erase_reification_safety; apply Hτr₀
    apply sem_soundness
    apply sem_reification_preservation
    apply Hstep; apply Hτr₀

-- e₀ ↦ e₁
-- ∅ ⊢ e₀ : τ
-- ∅ ⊢ C⟦∅ ⊢ ‖τ‖⟧ : ℕ
-- ————————————————————————————————
-- ∀ v. C⟦‖e₀‖⟧ ↦* v ↔ C⟦‖e₁‖⟧ ↦* v
theorem obs_preservation :
  ∀ e₀ e₁ τ φ,
    stepn e₀ e₁ →
    typing_reification [] e₀ τ φ →
    ∀ C, ObsCtxℂ [] ‖τ‖𝜏 C [] .nat →
    ∀ v, value v →
      (stepn C⟦‖e₀‖⟧ v ↔ stepn C⟦‖e₁‖⟧ v) :=
  by
  intros e₀ e₁ τ φ Hstepn Hτr₀
  have ⟨_, Hτr₁, _⟩ := preservation_stepn _ _ _ _ Hstepn Hτr₀
  have Hτ₀ := erase_reification_safety _ _ _ _ Hτr₀
  have Hτ₁ := erase_reification_safety _ _ _ _ Hτr₁
  rw [← erase_typing_reification_iff_typing] at Hτ₀ Hτ₁
  apply obs_stepn _ _ _ _ Hstepn Hτr₀ Hτ₀ Hτ₁

theorem obs_preservation_rep :
  ∀ e₀ v τ φ,
    stepn e₀ v →
    value v →
    typing_reification [] e₀ (.rep τ) φ →
    ∃ e₁,
      v = .code e₁ ∧
      ∀ C, ObsCtxℂ [] ‖τ‖𝜏 C [] .nat →
      ∀ v, value v →
        (stepn C⟦‖e₀‖⟧ v ↔ stepn C⟦e₁⟧ v) :=
  by
  intros e₀ v τ φ Hstepn Hvalue Hτr₀
  have ⟨_, Hτr₁, _⟩ := preservation_stepn _ _ _ _ Hstepn Hτr₀
  have ⟨e₁, HEq, Hτe₁⟩ := typing_rep_value _ _ _ Hvalue Hτr₁
  rw [HEq] at Hstepn
  exists e₁
  constructor; apply HEq
  rw [← typing_dyn_erase_id _ _ _ _ Hτe₁]
  apply obs_preservation _ _ _ _ Hstepn Hτr₀
