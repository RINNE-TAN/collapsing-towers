import CollapsingTowers.TwoLevelRec.LogicalEquiv.Defs
import CollapsingTowers.TwoLevelRec.Erasure.Defs

lemma consistency.head :
  ∀ Γ e₀ e₁ τ φ,
    head e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ →
    log_equiv ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏 :=
  by
  intros Γ e₀ e₁ τ φ Hhead Hτ₀
  have Hτ₁ := preservation.head _ _ _ _ _ Hhead Hτ₀
  constructor
  -- left hand side
  . cases Hhead <;> try apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₀
    case lets e bᵥ HvalueBind =>
      --
      --
      -- Γ ⊢ lets x = bᵥ in e : τ
      -- Γ ⊢ (x ↦ bᵥ)e : τ
      -- —————————————————————————————————————————————
      -- ‖Γ‖ ⊢ lets x = ‖bᵥ‖ in ‖e‖ : ‖τ‖
      -- ‖Γ‖ ⊢ (x ↦ ‖bᵥ‖)‖e‖ : ‖τ‖
      -- ‖Γ‖ ⊧ (x ↦ ‖bᵥ‖)‖e‖ ≤𝑙𝑜𝑔 (x ↦ ‖bᵥ‖)‖e‖ : ‖τ‖
      have Hτ₀ := typing.erase_safety _ _ _ _ _ Hτ₀
      have Hτ₁ := typing.erase_safety _ _ _ _ _ Hτ₁
      have ⟨_, _, IH⟩ := log_approx.fundamental _ _ _ Hτ₁
      simp only [log_approx_expr] at IH
      constructor; apply Hτ₀
      constructor; apply Hτ₁
      intros k γ₀ γ₁ HsemΓ
      simp only [log_approx_expr]
      intros j Hindexj v₀ Hvalue₀ Hstep₀
      --
      --
      -- lets x = γ₀‖bᵥ‖ in γ₀‖e‖ ⇝ ⟦j⟧ v₀
      -- —————————————————————————————————
      -- i + 1 = j
      -- (x ↦ γ₀‖bᵥ‖, γ₀)‖e‖ ⇝ ⟦i⟧ v₀
      admit
    case app₁ =>
      admit
    case lift_lam e =>
      have HEq : ‖.lam𝕔 (maping𝕔 0 e)‖ = ‖.lift (.lam e)‖ :=
        by simp [identity.erase_maping𝕔]
      rw [HEq]
      apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₀
    case fix₁ f HvalueFix =>
      admit
  -- right hand side
  . cases Hhead <;> try apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₁
    case lets e v Hvalue =>
      admit
    case app₁ =>
      admit
    case lift_lam e =>
      have HEq : ‖.lam𝕔 (maping𝕔 0 e)‖ = ‖.lift (.lam e)‖ :=
        by simp [identity.erase_maping𝕔]
      rw [← HEq]
      apply log_approx.fundamental; apply typing.erase_safety; apply Hτ₁
    case fix₁ =>
      admit
