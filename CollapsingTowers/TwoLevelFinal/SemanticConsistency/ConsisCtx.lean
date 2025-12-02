import CollapsingTowers.TwoLevelFinal.LogicalEquiv.Defs

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
  cases HB <;> try contradiction
  case appl₁ =>
    cases Hτ
    case app₁ Harg HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.app₁
        . assumption
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ HX Hf =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hf
        . assumption
  case appl₂ =>
    cases Hτ
    case app₂ HX Harg =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.app₁
        . assumption
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ Hf HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hf
        . assumption
  case binaryl₁ =>
    cases Hτ
    case binary₁ HX Hr =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.binary₁
        . assumption
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hr
  case binaryr₁ =>
    cases Hτ
    case binary₁ Hl HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.binary₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hl
        . assumption
  case binaryl₂ HX Hr =>
    cases Hτ
    case binary₂ HX Hr =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.binary₁
        . assumption
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hr
  case binaryr₂ =>
    cases Hτ
    case binary₂ Hl HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.binary₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hl
        . assumption
  case lift =>
    cases Hτ
    case lift_lam HX => apply IH _ _ HX
    case lift_lit HX => apply IH _ _ HX
    case lift_unit HX => apply IH _ _ HX
  case lets Hlc =>
    cases Hτ
    case lets τ𝕒 _ _ _ HX Hclosed He =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.lets
        . apply grounded_ty.under_erase τ𝕒
        . rw [← erase_env.length, ← closed.under_erase]
          apply Hclosed
        . rw [← erase_env.length, ← closed.under_erase]
          apply Hclosed
        . assumption
        . rw [← erase_env.length, ← erase_env, ← comm.erase_opening]
          apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ He
  case fix₁ =>
    cases Hτ
    case fix₁ HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.fix₁; assumption
  case fix₂ =>
    cases Hτ
    case fix₂ HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.fix₁; assumption
  case ifz₁ =>
    cases Hτ
    case ifz₁ HX Hl Hr =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.ifz₁
        . assumption
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hl
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hr
  case ifz₂ =>
    cases Hτ
    case ifz₂ HX Hl Hr =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.ifz₁
        . assumption
        . apply log_approx.fundamental
          apply typing_reification.erase.safety _ _ _ _ Hl
        . apply log_approx.fundamental
          apply typing_reification.erase.safety _ _ _ _ Hr
  case load₂ =>
    cases Hτ
    case load₂ HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.load₁; assumption
  case alloc₂ =>
    cases Hτ
    case alloc₂ HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.alloc₁; assumption
  case storel₂ =>
    cases Hτ
    case store₂ HX Hr =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.store₁
        . assumption
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hr
  case storer₂ =>
    cases Hτ
    case store₂ Hl HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor; all_goals
      . apply compatibility.store₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hl
        . assumption

-- Γ ⊢ e₀ : τ →
-- ‖Γ‖ ⊨ ‖e₀‖ ≈𝑙𝑜𝑔 ‖e₁‖ : ‖τ‖
-- ———————————————————————————————
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
        have ⟨IH₀, IH₁⟩ := IH (_ :: Γ) _ _ (by simp) HX
        have ⟨Hτ₀, Hτ₁, _⟩ := IH₀
        have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
        have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
        simp [← lc.under_erase] at Hlc₀ Hlc₁
        simp [← erase_env.length] at Hclosed₀ Hclosed₁
        constructor; all_goals
        . apply compatibility.lam
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
        have ⟨IH₀, IH₁⟩ := IH (_ :: Γ) _ _ (by simp) HX
        have ⟨Hτ₀, Hτ₁, _⟩ := IH₀
        have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
        have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
        simp [← lc.under_erase] at Hlc₀ Hlc₁
        simp [← erase_env.length] at Hclosed₀ Hclosed₁
        constructor; all_goals
        . apply compatibility.lets
          . apply grounded_ty.under_erase τ𝕒
          . rw [← erase_env.length, comm.erase_closing, ← closed.under_closing]
            assumption
          . rw [← erase_env.length, comm.erase_closing, ← closed.under_closing]
            assumption
          . apply log_approx.fundamental
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
  case ifzl₂ =>
    cases Hτ
    case ifz₂ Hc HX Hr =>
      cases HX
      all_goals next HX =>
      have ⟨IH₀, IH₁⟩ := IH Γ _ _ (by simp) HX
      constructor; all_goals
      . apply compatibility.ifz₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hc
        . assumption
        . apply log_approx.fundamental
          apply typing_reification.erase.safety _ _ _ _ Hr
  case ifzr₂ =>
    cases Hτ
    case ifz₂ Hc Hl HX =>
      cases HX
      all_goals next HX =>
      have ⟨IH₀, IH₁⟩ := IH Γ _ _ (by simp) HX
      constructor; all_goals
      . apply compatibility.ifz₁
        . apply log_approx.fundamental
          apply typing.erase.safety _ _ _ _ _ Hc
        . apply log_approx.fundamental
          apply typing_reification.erase.safety _ _ _ _ Hl
        . assumption
