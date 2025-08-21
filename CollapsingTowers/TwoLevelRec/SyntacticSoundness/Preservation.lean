import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx
import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvHead

theorem preservation.strengthened :
  ∀ Γ e₀ e₁ τ φ₀,
    step_lvl Γ.length e₀ e₁ →
    typing_reification Γ e₀ τ φ₀ →
    ∃ φ₁,
      typing_reification Γ e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intro Γ e₀ e₁ τ φ₀
  intro Hstep Hτ
  cases Hstep
  case pure M e₀ e₁ HM Hlc Hhead =>
    have Hfv := head.fv_shrink _ _ Hhead
    have IHτ := fun Γ τ φ₀ => preservation.head Γ e₀ e₁ τ φ₀ Hhead
    cases Hτ
    case pure Hτ =>
      have ⟨φ₁, Hτ, Hφ⟩ := preservation.under_ctx𝕄 _ _ _ _ _ _ HM Hlc Hfv IHτ Hτ
      exists φ₁; constructor
      . cases φ₁ <;> simp at Hφ
        apply typing_reification.pure; apply Hτ
      . apply Hφ
    case reify Hτ =>
      have ⟨φ₁, Hτ, Hφ⟩ := preservation.under_ctx𝕄 _ _ _ _ _ _ HM Hlc Hfv IHτ Hτ
      exists φ₁; constructor
      . apply typing_reification.reify; apply Hτ
      . apply Hφ
  case reflect P E e HP HE Hlc =>
    admit
