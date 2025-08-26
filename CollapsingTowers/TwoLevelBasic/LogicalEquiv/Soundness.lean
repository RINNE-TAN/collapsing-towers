import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Fundamental
import CollapsingTowers.TwoLevelBasic.CtxEquiv.Defs

lemma log_equiv.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B e₀ e₁,
    log_equiv Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    log_equiv Γ B⟦e₀⟧ B⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ B e₀ e₁ HX HB
  have ⟨Hτ₀, Hτ₁, Hsem_expr⟩ := HX
  induction HB generalizing e₀ e₁
  case lam Hwbt =>
    apply compatibility.lam
    . apply Hwbt
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . rw [identity.opening_closing, identity.opening_closing]
      apply HX
      apply typing.regular; apply Hτ₁
      apply typing.regular; apply Hτ₀
  case appl₁ Harg =>
    apply compatibility.app₁
    . apply HX
    . apply log_equiv.fundamental _ _ _ Harg
  case appr₁ Hf =>
    apply compatibility.app₁
    . apply log_equiv.fundamental _ _ _ Hf
    . apply HX
  case letsl τ𝕒 τ𝕓 Hclosed He =>
    apply compatibility.lets
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτ₀
      apply Hwbt
    . apply Hclosed
    . apply Hclosed
    . apply HX
    . apply log_equiv.fundamental _ _ _ He
  case letsr τ𝕒 τ𝕓 Hb =>
    apply compatibility.lets
    . have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hb
      apply Hwbt
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . apply log_equiv.fundamental _ _ _ Hb
    . rw [identity.opening_closing, identity.opening_closing]
      apply HX
      apply typing.regular; apply Hτ₁
      apply typing.regular; apply Hτ₀

-- Δ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ————————————————————————
-- Γ ⊧ C⟦e₀⟧ ≈𝑙𝑜𝑔 C⟦e₁⟧ : τγ
lemma log_equiv.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    log_equiv Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    log_equiv Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hsem HC
  induction HC generalizing e₀ e₁
  case hole => apply Hsem
  case cons𝔹 HB IH =>
    apply IH
    apply log_equiv.congruence_under_ObsCtx𝔹
    apply Hsem; apply HB

-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
theorem log_equiv.soundness :
  ∀ Γ τ e₀ e₁,
    log_equiv Γ e₀ e₁ τ →
    ctx_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hsem
  constructor; apply Hsem.left
  constructor; apply Hsem.right.left
  generalize HEqΔ : [] = Δ
  generalize HEqτδ : Ty.nat = τδ
  intros C HC v Hvalue
  induction HC generalizing e₀ e₁
  case hole =>
    rw [← HEqΔ, ← HEqτδ] at Hsem
    have ⟨Hτ₀, Hτ₁, Hsem_expr⟩ := Hsem
    simp only [log_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := Hsem_expr _ _ log_equiv_env.nil
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor
    . intro Hstep
      rw [← stepn.unique_normal_forms _ _ _ Hstep₀ Hstep (value.lit _), Hsem_value]
      apply Hstep₁; apply Hvalue
    . intro Hstep
      rw [← stepn.unique_normal_forms _ _ _ Hstep₁ Hstep (value.lit _), ← Hsem_value]
      apply Hstep₀; apply Hvalue
  case cons𝔹 C B HC HB IH =>
    apply IH
    apply log_equiv.congruence_under_ObsCtx𝔹
    apply Hsem; apply HB; apply HEqΔ; apply HEqτδ
