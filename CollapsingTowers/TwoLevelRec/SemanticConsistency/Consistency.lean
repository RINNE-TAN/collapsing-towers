import CollapsingTowers.TwoLevelRec.SemanticConsistency.ConsisHead
import CollapsingTowers.TwoLevelRec.SemanticConsistency.ConsisCtx

-- e₀ ⇝ e₁ (under Γ)
-- Γ ⊢ e₀ : τ
-- ———————————————————————
-- ‖Γ‖ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
theorem consistency.strengthened :
  ∀ Γ e₀ e₁ τ φ,
    step_lvl Γ.length e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros Γ e₀ e₁ τ φ
  generalize HEqlvl : Γ.length = lvl
  intros Hstep Hτ
  cases Hstep
  case pure HM Hlc Hhead =>
    induction HM generalizing Γ τ φ
    case hole =>
      apply consistency.head
      apply Hhead; apply Hτ
    case cons𝔹 B M HB HM IH =>
      rw [← ctx_comp B M, ← ctx_comp B M]
      apply consistency.under_ctx𝔹; apply HB
      intros _ _; apply IH
      apply HEqlvl; apply Hτ
    case consℝ R M HR HM IH =>
      rw [← ctx_comp R M, ← ctx_comp R M]
      apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
      apply lc.under_ctx𝕄; apply HM; apply Hlc
      intros _ _ _ HEqintro; apply IH
      simp; omega; apply Hτ
  case reflect HP HE Hlc =>
    cases HP
    case hole =>
      all_goals admit
    case consℚ HQ =>
      induction HQ generalizing Γ τ φ
      case holeℝ HR =>
        apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ _ Hτ
        all_goals admit
      case cons𝔹 B Q HB HQ IH =>
        rw [← ctx_comp B Q]
        apply consistency.under_ctx𝔹; apply HB
        intros _ _; apply IH
        apply HEqlvl; apply Hτ
      case consℝ R Q HR HQ IH =>
        rw [← ctx_comp R Q]
        apply consistency.under_ctxℝ; rw [HEqlvl]; apply HR
        apply lc.under_ctxℚ; apply HQ
        apply lc.under_ctx𝔼; apply HE; apply Hlc
        intros _ _ _ HEqintro; apply IH
        simp; omega; apply Hτ
