import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Defs

-- Γ ⊢ e₀ : τ →
-- ‖Γ‖ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
-- ———————————————————————————————
-- Γ ⊢ B⟦e₀⟧ : τ →
-- ‖Γ‖ ⊨ ‖B⟦e₀⟧‖ ≈𝑙𝑜𝑔 ‖B⟦e₁⟧‖ : ‖τ‖

lemma consistency.under_ctx𝔹 :
  ∀ Γ B e₀ e₁ τ φ,
    ctx𝔹 B →
    (∀ τ φ,
      typing Γ 𝟙 e₀ τ φ →
      log_equiv (erase_env Γ) ‖e₀‖ ‖e₁‖ (erase_ty τ)
    ) →
    typing Γ 𝟙 B⟦e₀⟧ τ φ →
    log_equiv (erase_env Γ) ‖B⟦e₀⟧‖ ‖B⟦e₁⟧‖ (erase_ty τ) :=
  by
  intros Γ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ Harg HX =>
      have IH := IH _ _ HX
      apply compatibility.app₁
      . assumption
      . apply log_equiv.fundamental
        apply typing.erase.safety _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ HX Hf =>
      have IH := IH _ _ HX
      apply compatibility.app₁
      . apply log_equiv.fundamental
        apply typing.erase.safety _ _ _ _ _ Hf
      . assumption
  case appl₂ =>
    cases Hτ
    case app₂ HX Harg =>
      have IH := IH _ _ HX
      apply compatibility.app₁
      . assumption
      . apply log_equiv.fundamental
        apply typing.erase.safety _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ Hf HX =>
      have IH := IH _ _ HX
      apply compatibility.app₁
      . apply log_equiv.fundamental
        apply typing.erase.safety _ _ _ _ _ Hf
      . assumption
  case lift =>
    cases Hτ
    case lift_lam HX => apply IH _ _ HX
    case lift_lit HX => apply IH _ _ HX
  case lets Hlc =>
    cases Hτ
    case lets τ𝕒 _ _ _ HX Hclosed He =>
      have IH := IH _ _ HX
      apply compatibility.lets
      . apply grounded_ty.under_erase τ𝕒
      . rw [← erase_env.length, ← closed.under_erase]
        apply Hclosed
      . rw [← erase_env.length, ← closed.under_erase]
        apply Hclosed
      . assumption
      . rw [← erase_env.length, ← erase_env, ← comm.erase_opening]
        apply log_equiv.fundamental
        apply typing.erase.safety _ _ _ _ _ He

-- Γ ⊢ e₀ : τ →
-- ‖Γ‖ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
-- ————————————————————————————
-- Γ ⊢ R⟦e₀⟧ : τ →
-- ‖Γ‖ ⊨ ‖R⟦e₀⟧‖ ≈𝑙𝑜𝑔 ‖R⟦e₁⟧‖ : ‖τ‖
lemma consistency.under_ctxℝ :
  ∀ intro Γ R e₀ e₁ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    (∀ Δ τ φ,
      Δ.length = Γ.length + intro →
      typing Δ 𝟙 e₀ τ φ →
      log_equiv (erase_env Δ) ‖e₀‖ ‖e₁‖ (erase_ty τ)
    ) →
    typing Γ 𝟙 R⟦e₀⟧ τ φ →
    log_equiv (erase_env Γ) ‖R⟦e₀⟧‖ ‖R⟦e₁⟧‖ (erase_ty τ) :=
  by
  intros intro Γ R e₀ e₁ τ φ HR Hlc IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 Hwbt HX Hclosed =>
      cases HX
      all_goals next HX =>
        rw [← List.singleton_append, identity.opening_closing _ _ _ Hlc] at HX
        have IH := IH (_ :: Γ) _ _ (by simp) HX
        have ⟨Hτ₀, Hτ₁, _⟩ := IH
        have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
        have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
        simp [← lc.under_erase] at Hlc₀ Hlc₁
        simp [← erase_env.length] at Hclosed₀ Hclosed₁
        apply compatibility.lam
        . apply grounded_ty.under_erase
        . rw [← erase_env.length, comm.erase_closing, ← closed.under_closing]
          assumption
        . rw [← erase_env.length, comm.erase_closing, ← closed.under_closing]
          assumption
        . rw [← erase_env.length, ← comm.erase_opening, ← comm.erase_opening]
          rw [identity.opening_closing _ _ _ Hlc₀, identity.opening_closing _ _ _ Hlc₁]
          assumption
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 _ Hwbt Hτb HX Hclosed =>
      cases HX
      all_goals next HX =>
        rw [← List.singleton_append, identity.opening_closing _ _ _ Hlc] at HX
        have IH := IH (_ :: Γ) _ _ (by simp) HX
        have ⟨Hτ₀, Hτ₁, _⟩ := IH
        have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
        have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
        simp [← lc.under_erase] at Hlc₀ Hlc₁
        simp [← erase_env.length] at Hclosed₀ Hclosed₁
        apply compatibility.lets
        . apply grounded_ty.under_erase τ𝕒
        . rw [← erase_env.length, comm.erase_closing, ← closed.under_closing]
          assumption
        . rw [← erase_env.length, comm.erase_closing, ← closed.under_closing]
          assumption
        . apply log_equiv.fundamental
          apply typing.erase.safety; apply Hτb
        . rw [← erase_env.length, ← comm.erase_opening, ← comm.erase_opening]
          rw [identity.opening_closing _ _ _ Hlc₀, identity.opening_closing _ _ _ Hlc₁]
          assumption
  case run =>
    cases Hτ
    case run Hτ =>
      cases Hτ
      all_goals next HX =>
        apply IH Γ _ _ (by simp) HX
