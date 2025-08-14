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
    case app₁ Harg HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply IH₀
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Harg
      -- right approximation
      . apply compatibility.app₁
        . apply IH₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ HX Hf =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hf
        . apply IH₀
      -- right approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hf
        . apply IH₁
  case appl₂ =>
    cases Hτ
    case app₂ HX Harg =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply IH₀
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Harg
      -- right approximation
      . apply compatibility.app₁
        . apply IH₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ Hf HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor
      -- left approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hf
        . apply IH₀
      -- right approximation
      . apply compatibility.app₁
        . apply log_approx.fundamental
          apply typing.erase_safety _ _ _ _ _ Hf
        . apply IH₁
  case lift =>
    cases Hτ
    case lift_lam HX => apply IH _ _ HX
    case lift_lit HX => apply IH _ _ HX
  case lets Hlc =>
    cases Hτ
    case lets τ𝕒 _ _ _ HX Hclosed He =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
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
    case fix₁ HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor
      -- left approximation
      . apply compatibility.fix₁; apply IH₀
      -- right approximation
      . apply compatibility.fix₁; apply IH₁
  case fix₂ =>
    cases Hτ
    case fix₂ HX =>
      have ⟨IH₀, IH₁⟩ := IH _ _ HX
      constructor
      -- left approximation
      . apply compatibility.fix₁; apply IH₀
      -- right approximation
      . apply compatibility.fix₁; apply IH₁
