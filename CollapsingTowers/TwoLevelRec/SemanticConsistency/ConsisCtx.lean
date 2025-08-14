import CollapsingTowers.TwoLevelRec.LogicalEquiv.Defs
import CollapsingTowers.TwoLevelRec.Erasure.Defs

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
      log_equiv ‖Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏
    ) →
    typing Γ 𝟙 B⟦e₀⟧ τ φ →
    log_equiv ‖Γ‖𝛾 ‖B⟦e₀⟧‖ ‖B⟦e₁⟧‖ ‖τ‖𝜏 :=
  by
  intros Γ B e₀ e₁ τ φ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ Hτarg HτX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply IH₀
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτarg
      -- right approximation
      . apply compatibility.app₁
        . apply IH₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτarg
  case appr₁ =>
    cases Hτ
    case app₁ HτX Hτf =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτf
        . apply IH₀
      -- right approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτf
        . apply IH₁
  case appl₂ =>
    cases Hτ
    case app₂ HτX Hτarg =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply IH₀
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτarg
      -- right approximation
      . apply compatibility.app₁
        . apply IH₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτarg
  case appr₂ =>
    cases Hτ
    case app₂ Hτf HτX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτf
        . apply IH₀
      -- right approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hτf
        . apply IH₁
  case lift =>
    cases Hτ
    case lift_lam HτX => apply IH _ _ HτX
    case lift_lit HτX => apply IH _ _ HτX
  case lets Hlc =>
    cases Hτ
    case lets τ𝕒 _ _ _ HτX Hclosed He =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.lets
        . apply ty.erase.wbt _ τ𝕒
        . rw [← env.erase.length, ← closed.under_erase]
          apply Hclosed
        . rw [← env.erase.length, ← closed.under_erase]
          apply Hclosed
        . apply IH₀
        . rw [← env.erase.length, ← env.erase, ← comm.erase_opening]
          apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ He
      -- right approximation
      . apply compatibility.lets
        . apply ty.erase.wbt _ τ𝕒
        . rw [← env.erase.length, ← closed.under_erase]
          apply Hclosed
        . rw [← env.erase.length, ← closed.under_erase]
          apply Hclosed
        . apply IH₁
        . rw [← env.erase.length, ← env.erase, ← comm.erase_opening]
          apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ He
  case fix₁ =>
    cases Hτ
    case fix₁ HτX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.fix₁; apply IH₀
      -- right approximation
      . apply compatibility.fix₁; apply IH₁
  case fix₂ =>
    cases Hτ
    case fix₂ HτX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HτX
      constructor
      -- left approximation
      . apply compatibility.fix₁; apply IH₀
      -- right approximation
      . apply compatibility.fix₁; apply IH₁

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
      Δ.length = intro →
      typing (Δ ++ Γ) 𝟙 e₀ τ φ →
      log_equiv ‖Δ ++ Γ‖𝛾 ‖e₀‖ ‖e₁‖ ‖τ‖𝜏
    ) →
    typing Γ 𝟙 R⟦e₀⟧ τ φ →
    log_equiv ‖Γ‖𝛾 ‖R⟦e₀⟧‖ ‖R⟦e₁⟧‖ ‖τ‖𝜏 :=
  by
  intros intro Γ R e₀ e₁ τ φ HR Hlc IH Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 _ Hwbt Hτ Hclosed =>
      cases Hτ
      all_goals next HτX =>
        rw [← List.singleton_append, identity.opening_closing _ _ _ Hlc] at HτX
        have ⟨IH₀, IH₁⟩ := IH [(τ𝕒, 𝟚)] _ _ (by simp) HτX
        have ⟨Hτ₀, Hτ₁, _⟩ := IH₀
        have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
        have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
        simp [← lc.under_erase] at Hlc₀ Hlc₁
        simp [← env.erase.length] at Hclosed₀ Hclosed₁
        constructor
        -- left approximation
        . apply compatibility.lam
          . apply ty.erase.wbt
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₀
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₁
          . rw [← env.erase.length, ← comm.erase_opening, ← comm.erase_opening]
            rw [identity.opening_closing _ _ _ Hlc₀, identity.opening_closing _ _ _ Hlc₁]
            apply IH₀
        -- right approximation
        . apply compatibility.lam
          . apply ty.erase.wbt
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₁
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₀
          . rw [← env.erase.length, ← comm.erase_opening, ← comm.erase_opening]
            rw [identity.opening_closing _ _ _ Hlc₀, identity.opening_closing _ _ _ Hlc₁]
            apply IH₁
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 _ Hwbt Hτb Hτe Hclosed =>
      cases Hτe
      all_goals next HτX =>
        rw [← List.singleton_append, identity.opening_closing _ _ _ Hlc] at HτX
        have ⟨IH₀, IH₁⟩ := IH [(τ𝕒, 𝟚)] _ _ (by simp) HτX
        have ⟨Hτ₀, Hτ₁, _⟩ := IH₀
        have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
        have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
        simp [← lc.under_erase] at Hlc₀ Hlc₁
        simp [← env.erase.length] at Hclosed₀ Hclosed₁
        constructor
        -- left approximation
        . apply compatibility.lets
          . apply ty.erase.wbt _ τ𝕒
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₀
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₁
          . apply log_approx.fundamental
            apply typing.erase_safety; apply Hτb
          . rw [← env.erase.length, ← comm.erase_opening, ← comm.erase_opening]
            rw [identity.opening_closing _ _ _ Hlc₀, identity.opening_closing _ _ _ Hlc₁]
            apply IH₀
        -- right approximation
        . apply compatibility.lets
          . apply ty.erase.wbt _ τ𝕒
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₁
          . rw [← env.erase.length, comm.erase_closing, ← closed.under_closing]
            apply Hclosed₀
          . apply log_approx.fundamental
            apply typing.erase_safety; apply Hτb
          . rw [← env.erase.length, ← comm.erase_opening, ← comm.erase_opening]
            rw [identity.opening_closing _ _ _ Hlc₀, identity.opening_closing _ _ _ Hlc₁]
            apply IH₁
  case run =>
    cases Hτ
    case run Hτ =>
      cases Hτ
      all_goals next HτX =>
        apply IH [] _ _ (by simp) HτX
