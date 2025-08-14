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
    case consℝ => admit
  case reflect HP HE Hlc => admit
