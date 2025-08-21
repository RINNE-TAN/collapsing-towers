import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx
import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvHead
import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvReflect

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
    have Hfv : fv e₁ ⊆ fv e₀ := by apply head.fv_shrink; apply Hhead
    have IHτ :
      ∀ Γ τ φ₀,
        typing Γ 𝟚 e₀ τ φ₀ →
        ∃ φ₁,
          typing Γ 𝟚 e₁ τ φ₁ ∧
          φ₁ ≤ φ₀ :=
      by intros Γ τ φ₀; apply preservation.head; apply Hhead
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
    have Hlc : lc E⟦.reflect e⟧ := by apply lc.under_ctx𝔼; apply HE; apply Hlc
    have Hfv : fv (.lets𝕔 e E⟦.code (.bvar 0)⟧) ⊆ fv E⟦.reflect e⟧ :=
      by
      simp; constructor
      . apply fv.decompose_ctx𝔼 _ (.reflect e); apply HE
      . apply fv.under_ctx𝔼; apply HE; simp
    have IHτ :
      ∀ Γ intro R τ φ₀,
        ctxℝ intro Γ.length R →
        typing Γ 𝟚 R⟦E⟦.reflect e⟧⟧ τ φ₀ →
        ∃ φ₁,
          typing Γ 𝟚 R⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ τ φ₁ ∧
          φ₁ ≤ φ₀ :=
      by
      intros Γ intro R τ φ₀ HR
      apply preservation.reify; apply HR; apply Hlc; apply Hfv; intros _ _ _
      apply preservation.reflect; apply HE
    cases HP
    case hole => apply preservation.reflect _ _ _ _ _ HE Hτ
    case consℚ HQ =>
      cases Hτ
      case pure Hτ =>
        have ⟨φ₁, Hτ, Hφ⟩ := preservation.under_ctxℚ _ _ _ _ _ _ HQ Hlc Hfv IHτ Hτ
        exists φ₁; constructor
        . cases φ₁ <;> simp at Hφ
          apply typing_reification.pure; apply Hτ
        . apply Hφ
      case reify Hτ =>
        have ⟨φ₁, Hτ, Hφ⟩ := preservation.under_ctxℚ _ _ _ _ _ _ HQ Hlc Hfv IHτ Hτ
        exists φ₁; constructor
        . apply typing_reification.reify; apply Hτ
        . apply Hφ
