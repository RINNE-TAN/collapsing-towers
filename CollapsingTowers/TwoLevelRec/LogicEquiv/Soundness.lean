import CollapsingTowers.TwoLevelRec.LogicEquiv.Fundamental
import CollapsingTowers.TwoLevelRec.CtxEquiv.Defs

lemma logic_rel_typing.congruence_under_ObsCtx𝔹 :
  ∀ Δ Γ τδ τγ B e₀ e₁,
    typing Δ 𝟙 e₀ τδ ∅ →
    typing Δ 𝟙 e₁ τδ ∅ →
    logic_rel_typing Δ e₀ e₁ τδ →
    ObsCtx𝔹 Δ τδ B Γ τγ →
    logic_rel_typing Γ B⟦e₀⟧ B⟦e₁⟧ τγ :=
  by
  intros Δ Γ τδ τγ B e₀ e₁ Hτ₀ Hτ₁ Hsem HB
  induction HB generalizing e₀ e₁
  case lam =>
    apply compatibility.lam
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
    apply compatibility.app₁
    . apply Hsem
    . apply typing.fundamental _ _ _ _ _ Harg
  case appr₁ Hf =>
    apply compatibility.app₁
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
  case fix₁ =>
    apply compatibility.fix₁
    apply Hsem

-- Δ ⊢ e₀ : τδ
-- Δ ⊢ e₁ : τδ
-- Δ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τδ
-- Γ ⊢ C⟦Δ ⊢ τδ⟧ : τγ
-- ————————————————————————
-- Γ ⊧ C⟦e₀⟧ ≤𝑙𝑜𝑔 C⟦e₁⟧ : τγ
lemma logic_rel_typing.congruence_under_ObsCtxℂ :
  ∀ Δ Γ τδ τγ C e₀ e₁,
    typing Δ 𝟙 e₀ τδ ∅ →
    typing Δ 𝟙 e₁ τδ ∅ →
    logic_rel_typing Δ e₀ e₁ τδ →
    ObsCtxℂ Δ τδ C Γ τγ →
    logic_rel_typing Γ C⟦e₀⟧ C⟦e₁⟧ τγ :=
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
    . apply logic_rel_typing.congruence_under_ObsCtx𝔹
      apply Hτ₀; apply Hτ₁; apply Hsem; apply HB

-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ
-- ——————————————————
-- Γ ⊢ e₀ ≤𝑐𝑡𝑥 e₁ : τ
theorem logic_equiv_typing.soundness :
  ∀ Γ τ e₀ e₁,
    logic_rel_typing Γ e₀ e₁ τ →
    ctx_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hsem Hτ₀ Hτ₁ C
  generalize HEqΔ : [] = Δ
  intros τ𝕔 HC Htermination
  induction HC generalizing e₀ e₁
  case hole =>
    have ⟨v₀, Hvalue₀, Hstep₀⟩ := Htermination
    have ⟨k, Hstep₀⟩ := pure_stepn_impl_pure_stepn_indexed _ _ Hstep₀
    rw [← HEqΔ] at Hsem
    have ⟨Hwf₀, Hwf₁, Hsem_expr⟩ := Hsem
    simp only [logic_rel_expr] at Hsem_expr
    have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr (k + 1) _ _ (logic_rel_env.nil _) k (by omega) _ Hvalue₀ Hstep₀
    have ⟨_, Hvalue₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value
    exists v₁
  case cons𝔹 C B HC HB IH =>
    apply IH
    apply logic_rel_typing.congruence_under_ObsCtx𝔹
    apply Hτ₀; apply Hτ₁
    apply Hsem; apply HB
    apply typing.congruence_under_ObsCtx𝔹; apply Hτ₀; apply HB
    apply typing.congruence_under_ObsCtx𝔹; apply Hτ₁; apply HB
    apply HEqΔ; apply Htermination
