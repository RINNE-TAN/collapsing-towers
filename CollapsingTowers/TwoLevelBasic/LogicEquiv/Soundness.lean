import CollapsingTowers.TwoLevelBasic.LogicEquiv.Fundamental
import CollapsingTowers.TwoLevelBasic.CtxEquiv.Defs

lemma logic_equiv_typing.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B e₀ e₁,
    typing Δ 𝟙 e₀ τδ ∅ →
    typing Δ 𝟙 e₁ τδ ∅ →
    logic_equiv_typing Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    logic_equiv_typing Γ B⟦e₀⟧ B⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ B e₀ e₁ Hτ₀ Hτ₁ Hsem HB
  induction HB generalizing e₀ e₁
  case lam =>
    apply compatibility_lam
    . simp; rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . simp; rw [← closed.under_closing]
      apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . rw [← env.erase.length]
      rw [identity.opening_closing, identity.opening_closing]
      apply Hsem
      apply typing.regular; apply Hτ₁
      apply typing.regular; apply Hτ₀
  case appl₁ Harg =>
    apply compatibility_app
    . apply Hsem
    . apply typing.fundamental _ _ _ _ _ Harg
  case appr₁ Hf =>
    apply compatibility_app
    . apply typing.fundamental _ _ _ _ _ Hf
    . apply Hsem
  case letsl Hclosed He =>
    apply compatibility.lets
    . constructor
      . apply typing.closed_at_env; apply Hτ₀
      . apply Hclosed
    . constructor
      . apply typing.closed_at_env; apply Hτ₁
      . apply Hclosed
    . apply Hsem
    . rw [← comm.erase_opening]
      rw [← comm.erase_opening] at He
      apply typing.fundamental _ _ _ _ _ He
  case letsr Hb =>
    apply compatibility.lets
    . constructor
      . apply typing.closed_at_env; apply Hb
      . rw [← closed.under_closing]
        apply typing.closed_at_env _ _ _ _ _ Hτ₀
    . constructor
      . apply typing.closed_at_env; apply Hb
      . rw [← closed.under_closing]
        apply typing.closed_at_env _ _ _ _ _ Hτ₁
    . apply typing.fundamental _ _ _ _ _ Hb
    . rw [identity.opening_closing, identity.opening_closing]
      apply Hsem
      apply typing.regular; apply Hτ₁
      apply typing.regular; apply Hτ₀

-- Δ ⊢ e₀ : τδ
-- Δ ⊢ e₁ : τδ
-- Δ ⊢ e₀ ≈ e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ——————————————————————
-- Γ ⊢ C⟦e₀⟧ ≈ C⟦e₁⟧ : τγ
lemma logic_equiv_typing.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    typing Δ 𝟙 e₀ τδ ∅ →
    typing Δ 𝟙 e₁ τδ ∅ →
    logic_equiv_typing Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    logic_equiv_typing Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ C e₀ e₁ Hτ₀ Hτ₁ Hsem HC
  induction HC generalizing e₀ e₁
  case hole => apply Hsem
  case cons𝔹 HB IH =>
    apply IH
    . apply typing.congruence_under_ObsCtx𝔹
      apply Hτ₀; apply HB
    . apply typing.congruence_under_ObsCtx𝔹
      apply Hτ₁; apply HB
    . apply logic_equiv_typing.congruence_under_ObsCtx𝔹
      apply Hτ₀; apply Hτ₁; apply Hsem; apply HB

-- Γ ⊧ e₀ ≈ e₁ : τ
-- ——————————————————
-- Γ ⊢ e₀ ≈𝑐𝑡𝑥 e₁ : τ
theorem logic_equiv_typing.soundness :
  ∀ Γ τ e₀ e₁,
    logic_equiv_typing Γ e₀ e₁ τ →
    ctx_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hsem Hτ₀ Hτ₁ C
  generalize HEqΔ : [] = Δ
  generalize HEqτδ : Ty.nat = τδ
  intros HC v Hvalue
  induction HC generalizing e₀ e₁
  case hole =>
    rw [← HEqΔ, ← HEqτδ] at Hsem
    have ⟨Hwf₀, Hwf₁, Hsem⟩ := Hsem
    have Hsem_expr := Hsem _ _ logic_equiv_env.nil
    rw [logic_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    have Hstepv₀ := pure_stepn_impl_stepn _ _ Hstepv₀
    have Hstepv₁ := pure_stepn_impl_stepn _ _ Hstepv₁
    constructor
    . intro Hstepv
      rw [← unique_normal_forms _ _ _ Hstepv₀ Hstepv, Hsem_value]
      apply Hstepv₁
      . apply value.lit
      . apply Hvalue
    . intro Hstepv
      rw [← unique_normal_forms _ _ _ Hstepv₁ Hstepv, ← Hsem_value]
      apply Hstepv₀
      . apply value.lit
      . apply Hvalue
  case cons𝔹 C B HC HB IH =>
    apply IH
    apply logic_equiv_typing.congruence_under_ObsCtx𝔹
    apply Hτ₀; apply Hτ₁
    apply Hsem; apply HB
    apply typing.congruence_under_ObsCtx𝔹; apply Hτ₀; apply HB
    apply typing.congruence_under_ObsCtx𝔹; apply Hτ₁; apply HB
    apply HEqΔ; apply HEqτδ
